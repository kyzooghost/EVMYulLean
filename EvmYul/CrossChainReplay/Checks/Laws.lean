import EvmYul.CrossChainReplay.Checks.Fixtures

/-! Non-vacuity check: the finite toy adapter satisfies every local law group, so the law
conjunction is not contradictory. This says nothing about an actual EVM revision. -/

open EvmYul.CrossChainReplay

theorem toyProtocolViewLaws : ProtocolViewLaws Toy := by
  refine ⟨?_, fun w => rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [Toy]

theorem toyDeterminismLaws : DeterminismLaws Toy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro w f env act w₁ f₁ o₁ w₂ f₂ o₂ ⟨-, rfl, rfl, rfl⟩ ⟨-, rfl, rfl, rfl⟩; simp
  · rintro w f env a₁ a₂ w₁ f₁ o₁ w₂ f₂ o₂ ⟨rfl, -⟩ ⟨rfl, -⟩; rfl
  · rintro w f req w₁ c₁ w₂ c₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩; simp
  · rintro origin cw child parent out w₁ f₁ w₂ f₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩; simp
  · rintro origin cw child parent target out w₁ f₁ r₁ e₁ w₂ f₂ r₂ e₂
      ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl⟩; simp
  · rintro w env envelope w₁ f₁ e₁ w₂ f₂ e₂ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩; simp
  · rintro w envelope out w₁ e₁ w₂ e₂ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩; simp

theorem toyProgressLaws : ProgressLaws Toy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f env
    exact ⟨.continue, { w with steps := w.steps + 1 }, f, toyObservation, rfl, rfl, rfl, rfl⟩
  · intro w f req; exact ⟨w, (0 : Nat), rfl, rfl⟩
  · intro origin cw child parent out; exact ⟨origin, parent, rfl, rfl⟩
  · intro w f address salt code value
    exact .inr ⟨w, f, .exceptional (.other "toy creation"), [], rfl, rfl, rfl, rfl⟩
  · intro origin cw child parent target out
    exact ⟨origin, parent, .exceptional (.other "toy creation"), [], rfl, rfl, rfl, rfl⟩
  · intro w env envelope _; exact ⟨w, (0 : Nat), [], rfl, rfl, rfl⟩
  · intro _ _ _ _; trivial
  · intro w envelope outcome; exact ⟨w, [], rfl, rfl⟩

theorem toyRollbackLaws : RollbackLaws Toy := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro origin cw child parent out w' resumed _ ⟨rfl, rfl⟩; simp [Toy]
  · rintro origin cw child parent target out w' resumed result events ⟨rfl, rfl, rfl, rfl⟩ _
    simp [Toy]
  · intros; rfl
  · intros; rfl

theorem toyObservationLaws : ObservationLaws Toy := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ source target amount h; simp [toyObservation] at h
  · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ access h; simp [toyObservation] at h
  · rintro w f env action w' f' obs - loc h; simp [Toy] at h
  · rintro w f env action w' f' obs - address h; simp [Toy] at h
  · rintro w f env action w' f' obs ⟨-, -, -, rfl⟩ envelope; rfl
  · rintro w env envelope w' f events ⟨-, -, rfl⟩; rfl
  · rintro w env envelope w' f events - address h; simp [Toy] at h
  · rintro w envelope out w' events - address h; simp [Toy] at h

theorem toyResourceArithmeticLaws : ResourceArithmeticLaws Toy := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro before amount after ⟨h, rfl⟩; simp; omega
  · rintro before amount after ⟨h, rfl⟩; simp; omega
  · rintro before amount after rfl; rfl
  · rintro before source target amount after ⟨h, rfl⟩ hne
    refine ⟨?_, ?_, ?_⟩
    · simp [hne]; omega
    · simp [hne, Ne.symm hne]
    · intro other h1 h2; simp [hne, h1, h2]
  · rintro before address after rfl
    exact ⟨by simp, fun other h => by simp [h]⟩

/-- `toyInterfaceLaws`: every local law group holds for the toy adapter. -/
theorem toyInterfaceLaws : SemanticInterfaceLaws Toy toyParams :=
  ⟨toyProtocolViewLaws, toyDeterminismLaws, toyProgressLaws, toyRollbackLaws,
    toyObservationLaws, toyResourceArithmeticLaws⟩
