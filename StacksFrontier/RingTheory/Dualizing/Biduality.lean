module

public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom

/-!
# Biduality for a dualizing complex: the two missing bridges

The biduality criterion `Dualizing.isIso_dualizingBidualityMor` of [stacks 0A7C] reduces
invertibility of the canonical biduality morphism `K ⟶ RHom_A(RHom_A(K, ω), ω)` to invertibility
of two canonical morphisms: the derived homothety `A ⟶ RHom_A(ω, ω)`, which the dualizing
hypothesis of [stacks 0A7B] controls, and the internalized evaluation morphism of [stacks 0A67]
at `(K, ω, ω)`, which [stacks 0A69] controls. Neither hypothesis was reachable from the proved
form of the result controlling it. This file builds the two bridges.

For the evaluation morphism there are two obstructions. First, [stacks 0A67] is stated
existentially and [stacks 0A69] concludes invertibility of
`Classical.choose (StacksDraft.DerivedHom.exists_evaluationToIteratedDerivedHom)`, which is
opaque, so its conclusion cannot be fed to a criterion phrased in terms of
`StacksDraft.DerivedHom.DerivedHomAdjunction.internalCurryMor` even though `internalCurryMor` is
literally the chosen witness. Both families satisfy the same three naturality laws and the same
comparison on K-flat/K-injective representatives, so they agree at a triple of representatives;
invertibility is then moved to an arbitrary triple by
`StacksDraft.DerivedHom.DerivedHomAdjunction.isIso_of_naturality_of_iso`, which transports
invertibility of any family satisfying those naturality laws along isomorphisms in each of the
three variables. Second, [stacks 0A69] is proved for the single-universe adjunction
`StacksDraft.DerivedHom.derivedHomAdjunction`, whereas the biduality morphism of [stacks 0A7C]
belongs to `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is the transport of the
former along restriction of scalars from `ULift A`. Rather than transporting the evaluation
morphism, this file transports the biduality morphism itself: for an adjunction transported along
an additive equivalence, the biduality morphism at `(ω, K)` is the image of the biduality
morphism at the preimages, conjugated by the counit and by the inverse unit
(`Dualizing.bidualityMor_transport`). That reduces all of [stacks 0A7C]'s biduality to the
model-level adjunction over `ULift A`, where the unitor coherence of [stacks 0795] and
[stacks 0A69] are both available.

For the derived homothety the file supplies the model-theoretic half: invertibility is detected
at any pair of representatives of `ω` (`Dualizing.isIso_derivedHomothety_of_isIso_homEquiv_symm`),
and at a K-flat representative `L`, a K-injective representative `I` and a chain map
`f : L ⟶ I` between them the degree-zero identification of [stacks 0A62] turns the derived
homothety into the explicit chain map `Φ ≫ (λ ≫ f)_* : 1 ⟶ Hom^•_A(L, I)`
(`Dualizing.isIso_derivedHomothety_of_quasiIso`). The chain-level identification of that map with
the scalar homothety `A[0] ⟶ Hom^•_A(I, I)` whose quasi-isomorphy is the third field of
`Dualizing.IsDualizingComplex` is **not** proved here;
it is `Dualizing.homothetyModel_precomp` of
`StacksFrontier/RingTheory/Dualizing/DerivedHomothety/Homothety.lean`, which imports this file,
whence `Dualizing.isIso_derivedHomothety_of_injectiveRepresentative` and
`Dualizing.isIso_derivedHomothety_of_isDualizingComplex` there.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.isIso_of_naturality_of_iso` — invertibility of a
  naturality-respecting evaluation family transports along isomorphisms in all three variables.
* `StacksDraft.DerivedHom.isIso_internalCurryMor_of_isIso_evaluation` — the de-existentialized
  form of the conclusion of [stacks 0A67] and [stacks 0A69].
* `StacksDraft.DerivedHom.isIso_internalCurryMor_of_truncLE_pseudoCoherent` — [stacks 0A69]
  restated for `internalCurryMor`.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_symm_map` and
  `StacksDraft.DerivedHom.DerivedHomAdjunction.evaluation_transport` — transposition and
  evaluation under transport along an additive equivalence.
* `Dualizing.isIso_bidualityMor` — the biduality criterion for an abstract adjunction.
* `Dualizing.bidualityMor_transport` and `Dualizing.isIso_bidualityMor_transport` — the
  biduality morphism of a transported adjunction, and the resulting transport of invertibility.
* `Dualizing.homEquiv_symm_unitorLeft_comp`,
  `Dualizing.isIso_derivedHomothety_of_isIso_homEquiv_symm` and
  `Dualizing.isIso_derivedHomothety_of_quasiIso` — the derived homothety read at a pair of
  representatives, and its invertibility from a chain-level quasi-isomorphism.
* `Dualizing.isIso_dualizingBidualityMor_of_ulift` and
  `Dualizing.isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent` — biduality for the
  adjunction of [stacks 0A63], from the two hypotheses at the scalar preimages, and with the
  evaluation hypothesis discharged by [stacks 0A69].

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
* [Stacks Project, Tag 0A67](https://stacks.math.columbia.edu/tag/0A67)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksDraft.DerivedHom

namespace DerivedHomAdjunction

/-! ### Invertibility of an evaluation family is an isomorphism-invariant condition -/

section Naturality

universe u v w

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {d : DerivedHomAdjunction R}

/-- The derived-Hom bifunctor sends a pair of isomorphisms to an isomorphism. -/
public theorem isIso_hom_map {X X' : (DerivedCategory (ModuleCat.{v} R))ᵒᵖ}
    {Y Y' : DerivedCategory (ModuleCat.{v} R)} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsIso f] [IsIso g] :
    IsIso (d.hom.map (X := (X, Y)) (Y := (X', Y')) (f, g)) := by
  have : IsIso (show (X, Y) ⟶ (X', Y') from (f, g)) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- **Invertibility of an evaluation family is isomorphism-invariant.** Let `ev` be any family of
morphisms `RHom(L, M) ⊗ᴸ K ⟶ RHom(RHom(K, L), M)` which is natural in the tensor argument,
contravariantly natural in the middle argument and natural in the target — the three laws that
the internalized evaluation of [stacks 0A67] satisfies and that its existential statement
records. Then invertibility of `ev` at one triple of objects implies invertibility at any
isomorphic triple. -/
public theorem isIso_of_naturality_of_iso
    (ev : ∀ K L M : DerivedCategory (ModuleCat.{v} R),
      d.tensor.obj (d.hom.obj (Opposite.op L, M), K) ⟶
        d.hom.obj (Opposite.op (d.hom.obj (Opposite.op K, L)), M))
    (hleft : ∀ {K K' L M : DerivedCategory (ModuleCat.{v} R)} (f : K ⟶ K'),
      d.tensor.map (𝟙 (d.hom.obj (Opposite.op L, M)), f) ≫ ev K' L M =
        ev K L M ≫ d.hom.map ((d.hom.map (f.op, 𝟙 L)).op, 𝟙 M))
    (hmiddle : ∀ {K L L' M : DerivedCategory (ModuleCat.{v} R)} (f : L ⟶ L'),
      d.tensor.map (d.hom.map (f.op, 𝟙 M), 𝟙 K) ≫ ev K L M =
        ev K L' M ≫ d.hom.map ((d.hom.map (𝟙 (Opposite.op K), f)).op, 𝟙 M))
    (hright : ∀ {K L M M' : DerivedCategory (ModuleCat.{v} R)} (f : M ⟶ M'),
      d.tensor.map (d.hom.map (𝟙 (Opposite.op L), f), 𝟙 K) ≫ ev K L M' =
        ev K L M ≫ d.hom.map (𝟙 (Opposite.op (d.hom.obj (Opposite.op K, L))), f))
    {K K' L L' M M' : DerivedCategory (ModuleCat.{v} R)}
    (iK : K ≅ K') (iL : L ≅ L') (iM : M ≅ M') (h : IsIso (ev K L M)) :
    IsIso (ev K' L' M') := by
  have : ∀ {X X' : (DerivedCategory (ModuleCat.{v} R))ᵒᵖ} {Y Y' : DerivedCategory (ModuleCat.{v} R)}
      (f : X ⟶ X') (g : Y ⟶ Y') [IsIso f] [IsIso g],
      IsIso (d.hom.map (X := (X, Y)) (Y := (X', Y')) (f, g)) := fun f g _ _ => isIso_hom_map f g
  have key : ∀ {A B C D : DerivedCategory (ModuleCat.{v} R)} {a : A ⟶ B} {x : B ⟶ C}
      {y : A ⟶ D} {b : D ⟶ C}, IsIso a → IsIso b → a ≫ x = y ≫ b → (IsIso x ↔ IsIso y) := by
    intro A B C D a x y b _ _ hab
    rw [← isIso_comp_left_iff a, hab, isIso_comp_right_iff]
  have hK : IsIso (ev K' L M) :=
    (key (isIso_tensor_map _ _) (isIso_hom_map _ _) (hleft iK.hom)).2 h
  have hL : IsIso (ev K' L' M) :=
    (key (isIso_tensor_map _ _) (isIso_hom_map _ _) (hmiddle iL.hom)).1 hK
  exact (key (isIso_tensor_map _ _) (isIso_hom_map _ _) (hright iM.hom)).2 hL

/-- **Invertibility of internalized evaluation is isomorphism-invariant.** This is
`isIso_of_naturality_of_iso` at the internalized evaluation morphism of [stacks 0A67], whose
three naturality laws are `internalCurryMor_naturality_left`,
`internalCurryMor_naturality_middle` and `internalCurryMor_naturality_right`. -/
public theorem isIso_internalCurryMor_of_iso
    {K K' L L' M M' : DerivedCategory (ModuleCat.{v} R)}
    (iK : K ≅ K') (iL : L ≅ L') (iM : M ≅ M')
    (h : IsIso (d.internalCurryMor K L M)) :
    IsIso (d.internalCurryMor K' L' M') :=
  isIso_of_naturality_of_iso d.internalCurryMor
    (fun f => d.internalCurryMor_naturality_left f)
    (fun f => d.internalCurryMor_naturality_middle f)
    (fun f => d.internalCurryMor_naturality_right f) iK iL iM h

end Naturality

end DerivedHomAdjunction

/-! ### The conclusion of [stacks 0A69], de-existentialized -/

section Deexistentialize

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- At a K-flat first representative and K-injective second and third representatives, the
evaluation family chosen by [stacks 0A67] is the internalized evaluation morphism: the
comparison clause of that tag and
`StacksDraft.DerivedHom.DerivedHomData.internalCurryMor_comparison` identify both with the same
composite of the chain-level evaluation map of [stacks 0A60]. -/
private theorem evaluationChoice_eq_internalCurryMor
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    [L.IsKInjective] [M.IsKInjective] :
    Classical.choose (exists_evaluationToIteratedDerivedHom (R := R))
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) =
      (derivedHomAdjunction (R := R)).toDerivedHomAdjunction.internalCurryMor
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) :=
  ((Classical.choose_spec
      (exists_evaluationToIteratedDerivedHom (R := R))).2.2.2 K L M hK).symm.trans
    ((derivedHomAdjunction (R := R)).internalCurryMor_comparison K L M hK).symm

/-- **The conclusion of [stacks 0A67] and [stacks 0A69], de-existentialized.** The evaluation
family of [stacks 0A67] is chosen by `Classical.choose`, so its invertibility cannot be fed
directly to a statement about `internalCurryMor`; but the two agree at K-flat/K-injective
representatives, and invertibility of either is isomorphism-invariant. -/
public theorem isIso_internalCurryMor_of_isIso_evaluation
    (K L M : DerivedCategory (ModuleCat.{u} R))
    (h : IsIso (Classical.choose (exists_evaluationToIteratedDerivedHom (R := R)) K L M)) :
    IsIso ((derivedHomAdjunction (R := R)).toDerivedHomAdjunction.internalCurryMor K L M) := by
  obtain ⟨P, hP, ⟨iP⟩⟩ := exists_kFlat_representative K
  obtain ⟨J, hJ, ⟨iJ⟩⟩ := exists_kInjective_model L
  obtain ⟨I, hI, ⟨iI⟩⟩ := exists_kInjective_model M
  have := hJ
  have := hI
  have hmodel : IsIso (Classical.choose (exists_evaluationToIteratedDerivedHom (R := R))
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I)) :=
    DerivedHomAdjunction.isIso_of_naturality_of_iso
      (d := (derivedHomAdjunction (R := R)).toDerivedHomAdjunction)
      (Classical.choose (exists_evaluationToIteratedDerivedHom (R := R)))
      (Classical.choose_spec (exists_evaluationToIteratedDerivedHom (R := R))).1
      (Classical.choose_spec (exists_evaluationToIteratedDerivedHom (R := R))).2.1
      (Classical.choose_spec (exists_evaluationToIteratedDerivedHom (R := R))).2.2.1
      iP.symm iJ.symm iI.symm h
  rw [evaluationChoice_eq_internalCurryMor P J I hP] at hmodel
  exact DerivedHomAdjunction.isIso_internalCurryMor_of_iso iP iJ iI hmodel

/-- **Stacks 0A69, for the internalized evaluation morphism.** The internalized evaluation
morphism `RHom_R(L, M) ⊗ᴸ_R K ⟶ RHom_R(RHom_R(K, L), M)` of [stacks 0A67] is an isomorphism if
`L` and `M` have finite injective dimension, `RHom_R(L, M)` has finite Tor dimension, and every
truncation `τ_{≤ n} K` is pseudo-coherent. -/
public theorem isIso_internalCurryMor_of_truncLE_pseudoCoherent
    (K L M : DerivedCategory (ModuleCat.{u} R))
    (hL : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension L)
    (hM : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension M)
    (hTor :
      let D := derivedHomAdjunction (R := R)
      ∃ a b : ℤ, ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (D.tensor.obj
            (D.hom.obj (Opposite.op L, M),
              (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N))))
    (hK : ∀ n : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.TStructure.t.truncLE n).obj K)) :
    IsIso ((derivedHomAdjunction (R := R)).toDerivedHomAdjunction.internalCurryMor K L M) :=
  isIso_internalCurryMor_of_isIso_evaluation K L M
    (evaluationToIteratedDerivedHom_isIso_of_truncLE_pseudoCoherent K L M hL hM hTor hK)

end Deexistentialize

/-! ### Transport of transposes and of evaluation along an equivalence -/

section UnitObject

universe u₃ v₃ u₄ v₄

/-- The inverse of the unit of an equivalence at an object, as an isomorphism whose source is
spelled as an iterated object application rather than through the composite functor. The two
spellings are definitionally equal, but a morphism fed to a bifunctor must present its source in
the shape the bifunctor expects, and the composite-functor spelling does not. -/
public def equivalenceUnitObjIso {C : Type u₃} {D : Type u₄} [Category.{v₃} C] [Category.{v₄} D]
    (e : C ≌ D) (X : C) : e.inverse.obj (e.functor.obj X) ≅ X := (e.unitIso.app X).symm

end UnitObject

namespace DerivedHomAdjunction

section Transport

universe u₁ v₁ w₁ u₂ v₂ w₂

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
    (d : DerivedHomAdjunction R)
    (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
    [e.functor.Additive]

omit [e.functor.Additive] in
/-- A morphism into the image of the inverse equivalence, pushed forward, composed with the
counit and pulled back again, is recovered by the unit. -/
private theorem unit_inverse_map_functor_counit {X : DerivedCategory (ModuleCat.{v₁} R)}
    (M : DerivedCategory (ModuleCat.{v₂} S)) (w : X ⟶ e.inverse.obj M) :
    e.unit.app X ≫ e.inverse.map (e.functor.map w ≫ e.counitIso.hom.app M) = w := by
  rw [e.inverse.map_comp, reassoc_of% (Equivalence.unit_naturality e w),
    Equivalence.unit_inverse_comp, Category.comp_id]

omit [e.functor.Additive] in
/-- The counit at an image object cancels against the image of the inverse unit. -/
private theorem counitInv_comp_map_unitObjIso (X : DerivedCategory (ModuleCat.{v₁} R)) :
    e.counitInv.app (e.functor.obj X) ≫ e.functor.map (equivalenceUnitObjIso e X).hom =
      𝟙 (e.functor.obj X) := by
  change e.counitInv.app (e.functor.obj X) ≫ e.functor.map (e.unitIso.inv.app X) = _
  rw [Equivalence.counitInv_app_functor, ← e.functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  rfl

/-- `transportHomEquiv_symm_map` for the transported Hom equivalence as it is built, before it is
read off as a field of the transported adjunction. Unfolding the structure instance leaves the
additive structure of the source of that equivalence spelled through
`StacksDraft.DerivedHom.DerivedHomAdjunction.transport` while its carrier is spelled through
`StacksDraft.DerivedHom.DerivedHomAdjunction.transportTensor`, and rewriting cannot proceed
through that mismatch; here there is nothing to unfold. -/
private theorem transportHomEquiv_symm_map' (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (g : d.tensor.obj (e.inverse.obj K, e.inverse.obj L) ⟶ e.inverse.obj M) :
    (d.transportHomEquiv e K L M).symm (e.functor.map g ≫ e.counitIso.hom.app M) =
      e.counitInv.app K ≫ e.functor.map
        ((d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).symm g) := by
  dsimp only [transportHomEquiv]
  rw [AddEquiv.symm_trans_apply, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    AddEquiv.symm_symm]
  simp only [Adjunction.homAddEquiv_apply, Adjunction.homEquiv_unit,
    Equivalence.toAdjunction_unit, Equivalence.symm_functor, Equivalence.symm_inverse,
    Equivalence.symm_unit]
  rw [unit_inverse_map_functor_counit e M g]

/-- **Transposition commutes with transport.** For an adjunction transported along an additive
equivalence, the inverse Hom equivalence of a morphism which is the image of a morphism of the
source category followed by the counit — and every morphism out of a transported tensor product
is of that form — is the image of the inverse Hom equivalence there, preceded by the counit. -/
public theorem transportHomEquiv_symm_map (K L M : DerivedCategory (ModuleCat.{v₂} S))
    (g : d.tensor.obj (e.inverse.obj K, e.inverse.obj L) ⟶ e.inverse.obj M) :
    ((d.transport e).homEquiv K L M).symm (e.functor.map g ≫ e.counitIso.hom.app M) =
      e.counitInv.app K ≫ e.functor.map
        ((d.homEquiv (e.inverse.obj K) (e.inverse.obj L) (e.inverse.obj M)).symm g) :=
  transportHomEquiv_symm_map' d e K L M g

/-- Transposing evaluation after tensoring with a morphism in the internal-Hom slot returns that
morphism: evaluation is the transpose of the identity, and transposition is natural in the tensor
argument. -/
private theorem homEquiv_symm_tensorMap_evaluation
    {X L M : DerivedCategory (ModuleCat.{v₁} R)} (u : X ⟶ d.hom.obj (Opposite.op L, M)) :
    (d.homEquiv X L M).symm (d.tensor.map (X := (X, L))
        (Y := (d.hom.obj (Opposite.op L, M), L)) (u, 𝟙 L) ≫ d.evaluation L M) = u := by
  apply (d.homEquiv X L M).injective
  rw [AddEquiv.apply_symm_apply, DerivedHomAdjunction.evaluation,
    ← d.homEquiv_naturality_left, Category.comp_id]

/-- **Evaluation commutes with transport.** The evaluation morphism of a transported adjunction
is the image of the evaluation morphism of the original one, corrected by the inverse unit of the
equivalence in the internal-Hom argument and by the counit in the target. -/
public theorem evaluation_transport (L M : DerivedCategory (ModuleCat.{v₂} S)) :
    (d.transport e).evaluation L M =
      e.functor.map (d.tensor.map
            (X := (e.inverse.obj (e.functor.obj
                (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))),
              e.inverse.obj L))
            (Y := (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M),
              e.inverse.obj L))
            ((equivalenceUnitObjIso e
                (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))).hom,
              𝟙 (e.inverse.obj L)) ≫
          d.evaluation (e.inverse.obj L) (e.inverse.obj M)) ≫
        e.counitIso.hom.app M := by
  have hid : ((d.transport e).homEquiv
        (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))) L M).symm
        (e.functor.map (d.tensor.map
              (X := (e.inverse.obj (e.functor.obj
                  (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))),
                e.inverse.obj L))
              (Y := (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M),
                e.inverse.obj L))
              ((equivalenceUnitObjIso e
                  (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))).hom,
                𝟙 (e.inverse.obj L)) ≫
            d.evaluation (e.inverse.obj L) (e.inverse.obj M)) ≫
          e.counitIso.hom.app M) =
      𝟙 (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))) := by
    rw [transportHomEquiv_symm_map, homEquiv_symm_tensorMap_evaluation]
    exact counitInv_comp_map_unitObjIso e _
  exact (congrArg (fun x => (d.transport e).homEquiv
      (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj L), e.inverse.obj M))) L M x)
    hid.symm).trans (AddEquiv.apply_symm_apply _ _)

end Transport

end DerivedHomAdjunction

end StacksDraft.DerivedHom

/-! ### Biduality: the abstract criterion and its transport -/

namespace Dualizing

open StacksDraft.DerivedHom

section AbstractCriterion

universe u₁ v₁ w₁

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v₁} R))
    (lam : ∀ K : DerivedCategory (ModuleCat.{v₁} R), d.tensor.obj (one, K) ≅ K)

/-- **The biduality criterion, for an abstract derived tensor--Hom adjunction.** This is
`Dualizing.isIso_dualizingBidualityMor` with the fixed adjunction of [stacks 0A63] replaced by an
arbitrary one carrying a tensor unit whose left unitor is natural and satisfies the
left-unitor/associator triangle: the canonical biduality morphism is invertible as soon as the
derived homothety `1 ⟶ RHom(ω, ω)` and the internalized evaluation morphism of [stacks 0A67] at
`(K, ω, ω)` are. -/
public theorem isIso_bidualityMor
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    (htri : ∀ K X : DerivedCategory (ModuleCat.{v₁} R),
      DerivedHomAdjunction.IsUnitorTriangleAt d one lam K X)
    (ω K : DerivedCategory (ModuleCat.{v₁} R))
    (hone : IsIso (derivedHomothety d one lam ω))
    (hcurry : IsIso (d.internalCurryMor K ω ω)) :
    IsIso (bidualityMor d ω K) := by
  have hone' := hone
  have hcurry' := hcurry
  have htensor : IsIso (d.tensor.map
      (X := (one, K)) (Y := (d.hom.obj (Opposite.op ω, ω), K))
      (derivedHomothety d one lam ω, 𝟙 K)) :=
    DerivedHomAdjunction.isIso_tensor_map _ _
  have hall : IsIso ((lam K).inv ≫ d.tensor.map
        (X := (one, K)) (Y := (d.hom.obj (Opposite.op ω, ω), K))
        (derivedHomothety d one lam ω, 𝟙 K) ≫
      d.internalCurryMor K ω ω) := inferInstance
  rw [bidualityMor_eq_internalCurryMor d one lam hlam htri ω K]
  exact hall

/-- Transposing evaluation after interchanging the two tensor factors and then tensoring with a
morphism into the internal Hom returns the canonical biduality morphism, corrected by that
morphism. This is the computation behind `Dualizing.bidualityMor_transport`, where the morphism
is the inverse unit of the equivalence; it uses only dinaturality of the Hom equivalence and
naturality of the tensor symmetry. -/
private theorem homEquiv_symm_tensorSwap_tensorMap_evaluation
    {X ω K : DerivedCategory (ModuleCat.{v₁} R)}
    (u : X ⟶ d.hom.obj (Opposite.op K, ω)) :
    (d.homEquiv K X ω).symm ((d.tensorSwap K X).hom ≫
        d.tensor.map (X := (X, K)) (Y := (d.hom.obj (Opposite.op K, ω), K)) (u, 𝟙 K) ≫
          d.evaluation K ω) =
      bidualityMor d ω K ≫ d.hom.map
        (X := (Opposite.op (d.hom.obj (Opposite.op K, ω)), ω))
        (Y := (Opposite.op X, ω)) (u.op, 𝟙 ω) := by
  apply (d.homEquiv K X ω).injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_dinaturality, bidualityMor,
    AddEquiv.apply_symm_apply, d.tensorSwap_naturality_assoc]

/-- The derived-Hom bifunctor applied to a composite pair of morphisms, with the pairs written
as named implicit arguments rather than through `show ... from`, which is the form the functor
laws present and hence the form `rw` can match. -/
private theorem hom_map_comp
    {A B C : (DerivedCategory (ModuleCat.{v₁} R))ᵒᵖ}
    {X Y Z : DerivedCategory (ModuleCat.{v₁} R)}
    (f : A ⟶ B) (g : B ⟶ C) (f' : X ⟶ Y) (g' : Y ⟶ Z) :
    d.hom.map (X := (A, X)) (Y := (B, Y)) (f, f') ≫
        d.hom.map (X := (B, Y)) (Y := (C, Z)) (g, g') =
      d.hom.map (X := (A, X)) (Y := (C, Z)) (f ≫ g, f' ≫ g') :=
  (d.hom.map_comp _ _).symm

/-- **The derived homothety read at a pair of representatives.** The transpose of the left
unitor followed by a morphism `X ⟶ ω` and the inverse of an isomorphism `Y ≅ ω` is the derived
homothety at `ω`, followed by derived Hom against that pair. Only naturality of the unitor
enters. -/
public theorem homEquiv_symm_unitorLeft_comp
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {X Y ω : DerivedCategory (ModuleCat.{v₁} R)} (α : X ⟶ ω) (β : Y ≅ ω) :
    (d.homEquiv one X Y).symm ((lam X).hom ≫ α ≫ β.inv) =
      derivedHomothety d one lam ω ≫
        d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, Y)) (α.op, β.inv) := by
  have hsplit : d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, Y))
        (α.op, β.inv) =
      d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, ω)) (α.op, 𝟙 ω) ≫
        d.hom.map (X := (Opposite.op X, ω)) (Y := (Opposite.op X, Y))
          (𝟙 (Opposite.op X), β.inv) := by
    rw [hom_map_comp]
    simp only [Category.comp_id, Category.id_comp]
  apply (d.homEquiv one X Y).injective
  rw [AddEquiv.apply_symm_apply, hsplit, ← Category.assoc (derivedHomothety d one lam ω),
    d.homEquiv_naturality_right, d.homEquiv_dinaturality, derivedHomothety,
    AddEquiv.apply_symm_apply, hlam α, Category.assoc]

/-- **Invertibility of the derived homothety is detected at any pair of representatives.** If
the transpose of the left unitor composed with an isomorphism `X ≅ ω` and the inverse of an
isomorphism `Y ≅ ω` is invertible, then so is the derived homothety at `ω`. -/
public theorem isIso_derivedHomothety_of_isIso_homEquiv_symm
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {X Y ω : DerivedCategory (ModuleCat.{v₁} R)} (α : X ≅ ω) (β : Y ≅ ω)
    (h : IsIso ((d.homEquiv one X Y).symm ((lam X).hom ≫ α.hom ≫ β.inv))) :
    IsIso (derivedHomothety d one lam ω) := by
  have hmap : IsIso (d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, Y))
      (α.hom.op, β.inv)) := DerivedHomAdjunction.isIso_hom_map (d := d) _ _
  have hcomp : IsIso (derivedHomothety d one lam ω ≫
      d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, Y)) (α.hom.op, β.inv)) := by
    rw [← homEquiv_symm_unitorLeft_comp d one lam hlam α.hom β]
    exact h
  exact IsIso.of_isIso_comp_right (derivedHomothety d one lam ω)
    (d.hom.map (X := (Opposite.op ω, ω)) (Y := (Opposite.op X, Y)) (α.hom.op, β.inv))

end AbstractCriterion

/-! ### The derived homothety at a chain-level model -/

section HomothetyModel

open CategoryTheory.MonoidalCategory

universe u₃

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u₃} [CommRing R] (d : DerivedHomData R)

/-- The derived homothety of a concrete model-level adjunction is the inverse degree-zero
identification of derived Hom, applied to the identity: both are the transpose of the left
unitor. -/
public theorem derivedHomothety_eq_homZeroEquiv_symm
    (ω : DerivedCategory (ModuleCat.{u₃} R)) :
    derivedHomothety d.toDerivedHomAdjunction
        (DerivedCategory.Q.obj (𝟙_ (Model.Complex R))) d.tensorUnitLeft ω =
      (d.homZeroEquiv ω ω).symm (𝟙 ω) := by
  change _ = (d.homEquiv _ ω ω).symm ((d.tensorUnitLeft ω).hom ≫ 𝟙 ω)
  rw [Category.comp_id, derivedHomothety]

/-- **The derived homothety is invertible as soon as its chain-level transpose is a
quasi-isomorphism.** Fix a K-flat representative `L` of `ω`, a K-injective representative `I`,
and a chain map `f : L ⟶ I` inducing the comparison between them. Then the degree-zero
identification of [stacks 0A62] carries `f` to the chain map
`Φ ≫ (λ ≫ f)_*` out of the complex unit, and invertibility of the derived homothety at `ω` is
exactly the statement that this chain map is a quasi-isomorphism. This is what the homothety
condition of [stacks 0A7B] is about: for `ω` a dualizing complex and `L = I` that chain map is
the scalar homothety `A[0] ⟶ Hom•(I, I)`. -/
public theorem isIso_derivedHomothety_of_quasiIso
    (ω : DerivedCategory (ModuleCat.{u₃} R)) (L I : Model.Complex R) (hL : L.KFlat)
    [I.IsKInjective] (f : L ⟶ I)
    (iL : DerivedCategory.Q.obj L ≅ ω) (iI : DerivedCategory.Q.obj I ≅ ω)
    (hf : DerivedCategory.Q.map f = iL.hom ≫ iI.inv)
    (hq : QuasiIso (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (Model.Complex R)) L ≫
      Stacks.HomComplex.TensorHomMap.postcomp R L (𝟙_ (Model.Complex R) ⊗ L) I ((λ_ L).hom ≫ f))) :
    IsIso (derivedHomothety d.toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex R))) d.tensorUnitLeft ω) := by
  have hQ : IsIso (DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.Phi R (𝟙_ (Model.Complex
    R)) L ≫
      Stacks.HomComplex.TensorHomMap.postcomp R L (𝟙_ (Model.Complex R) ⊗ L) I ((λ_ L).hom ≫ f))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hinv : IsIso (d.homIso L I).inv := inferInstance
  have hmodel : IsIso ((d.homZeroEquiv (DerivedCategory.Q.obj L)
      (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map f)) := by
    rw [d.homZeroEquiv_symm_map L I hL f]
    infer_instance
  refine isIso_derivedHomothety_of_isIso_homEquiv_symm d.toDerivedHomAdjunction
    (DerivedCategory.Q.obj (𝟙_ (Model.Complex R))) d.tensorUnitLeft
    (fun g => d.tensorUnitLeft_naturality g) iL iI ?_
  rw [← hf]
  exact hmodel

end HomothetyModel

section BidualityTransport

universe u₁ v₁ w₁ u₂ v₂ w₂

variable {R : Type u₁} [CommRing R] [HasDerivedCategory.{w₁} (ModuleCat.{v₁} R)]
    {S : Type u₂} [CommRing S] [HasDerivedCategory.{w₂} (ModuleCat.{v₂} S)]
    (d : DerivedHomAdjunction R)
    (e : DerivedCategory (ModuleCat.{v₁} R) ≌ DerivedCategory (ModuleCat.{v₂} S))
    [e.functor.Additive]

/-- **The canonical biduality morphism transports.** For an adjunction transported along an
additive equivalence of derived categories, the biduality morphism at `(ω, K)` is the image of
the biduality morphism at the preimages of `ω` and `K`, conjugated by the counit of the
equivalence and by the inverse unit in the inner derived-Hom argument. -/
public theorem bidualityMor_transport (ω K : DerivedCategory (ModuleCat.{v₂} S)) :
    bidualityMor (d.transport e) ω K =
      e.counitInv.app K ≫ e.functor.map
        (bidualityMor d (e.inverse.obj ω) (e.inverse.obj K) ≫
          d.hom.map
            (X := (Opposite.op (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)),
              e.inverse.obj ω))
            (Y := (Opposite.op (e.inverse.obj (e.functor.obj
                (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))),
              e.inverse.obj ω))
            ((equivalenceUnitObjIso e
                (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))).hom.op,
              𝟙 (e.inverse.obj ω))) := by
  have hbd : bidualityMor (d.transport e) ω K =
      ((d.transport e).homEquiv K
            (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))
            ω).symm
        (((d.transport e).tensorSwap K (e.functor.obj
              (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))).hom ≫
          (d.transport e).evaluation K ω) := rfl
  have hswap : ((d.transport e).tensorSwap K
        (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))).hom =
      e.functor.map ((d.tensorSwap (e.inverse.obj K) (e.inverse.obj (e.functor.obj
        (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))))).hom) := rfl
  have hstep : ((d.transport e).tensorSwap K
          (e.functor.obj (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))).hom ≫
        (d.transport e).evaluation K ω =
      e.functor.map ((d.tensorSwap (e.inverse.obj K) (e.inverse.obj (e.functor.obj
              (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))))).hom ≫
            d.tensor.map
              (X := (e.inverse.obj (e.functor.obj
                  (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))),
                e.inverse.obj K))
              (Y := (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω),
                e.inverse.obj K))
              ((equivalenceUnitObjIso e
                  (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))).hom,
                𝟙 (e.inverse.obj K)) ≫
            d.evaluation (e.inverse.obj K) (e.inverse.obj ω)) ≫
        e.counitIso.hom.app ω := by
    rw [hswap, DerivedHomAdjunction.evaluation_transport]
    simp only [e.functor.map_comp, Category.assoc]
    rfl
  rw [hbd, hstep]
  refine (DerivedHomAdjunction.transportHomEquiv_symm_map d e K _ ω _).trans ?_
  rw [homEquiv_symm_tensorSwap_tensorMap_evaluation]

/-- **Invertibility of biduality transports.** Invertibility of the canonical biduality morphism
at the preimages of `ω` and `K` gives invertibility of the biduality morphism of the transported
adjunction at `(ω, K)`: by `Dualizing.bidualityMor_transport` the latter differs from the image
of the former by the counit of the equivalence and by derived Hom against the inverse unit, both
of which are isomorphisms. -/
public theorem isIso_bidualityMor_transport (ω K : DerivedCategory (ModuleCat.{v₂} S))
    (h : IsIso (bidualityMor d (e.inverse.obj ω) (e.inverse.obj K))) :
    IsIso (bidualityMor (d.transport e) ω K) := by
  have h' := h
  have hhom : IsIso (d.hom.map
      (X := (Opposite.op (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)),
        e.inverse.obj ω))
      (Y := (Opposite.op (e.inverse.obj (e.functor.obj
          (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))),
        e.inverse.obj ω))
      ((equivalenceUnitObjIso e
          (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))).hom.op,
        𝟙 (e.inverse.obj ω))) :=
    DerivedHomAdjunction.isIso_hom_map (d := d) _ _
  have hall : IsIso (e.counitInv.app K ≫ e.functor.map
      (bidualityMor d (e.inverse.obj ω) (e.inverse.obj K) ≫
        d.hom.map
          (X := (Opposite.op (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)),
            e.inverse.obj ω))
          (Y := (Opposite.op (e.inverse.obj (e.functor.obj
              (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω)))),
            e.inverse.obj ω))
          ((equivalenceUnitObjIso e
              (d.hom.obj (Opposite.op (e.inverse.obj K), e.inverse.obj ω))).hom.op,
            𝟙 (e.inverse.obj ω)))) := inferInstance
  rw [bidualityMor_transport]
  exact hall

end BidualityTransport

/-! ### Biduality for the adjunction of [stacks 0A63] -/

section OverRing

universe u v

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory.MonoidalCategory

variable (A : Type u) [CommRing A]

/-- The canonical biduality morphism of [stacks 0A7C] is the transport, along the scalar
equivalence, of the biduality morphism of the model-level adjunction over the lifted ring:
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` is by construction that transport. -/
public theorem dualizingBidualityMor_eq_transport
    (ω K : DerivedCategory (ModuleCat.{max u v} A)) :
    dualizingBidualityMor.{u, v} A ω K =
      bidualityMor ((derivedHomAdjunctionULift.{u, v, max u v + 1}
          (R := A)).toDerivedHomAdjunction.transport (derivedScalarEquivalence.{u, v} A)) ω K :=
  rfl

/-- **The biduality criterion of [stacks 0A7C], reduced to the model-level adjunction over the
lifted ring.** The canonical biduality morphism is invertible as soon as the derived homothety
and the internalized evaluation morphism of [stacks 0A67] are invertible at the scalar preimages
of `ω` and `K`. The homothety hypothesis is the one
`Dualizing.isIso_derivedHomothety_overRing` already asks for; the evaluation hypothesis is what
[stacks 0A69] controls, through
`StacksDraft.DerivedHom.isIso_internalCurryMor_of_truncLE_pseudoCoherent`. -/
public theorem isIso_dualizingBidualityMor_of_ulift
    (ω K : DerivedCategory (ModuleCat.{max u v} A))
    (hone : IsIso (derivedHomothety
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))))
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).tensorUnitLeft
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω)))
    (hcurry : IsIso ((derivedHomAdjunctionULift.{u, v, max u v + 1}
        (R := A)).toDerivedHomAdjunction.internalCurryMor
      ((derivedScalarEquivalence.{u, v} A).inverse.obj K)
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω)
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω))) :
    IsIso (dualizingBidualityMor.{u, v} A ω K) := by
  rw [dualizingBidualityMor_eq_transport]
  exact isIso_bidualityMor_transport _ (derivedScalarEquivalence.{u, v} A) ω K
    (isIso_bidualityMor _ _ _ (derivedHomAdjunction_isUnitorNatural (R := ULift.{v} A))
      (derivedHomAdjunction_unitorTriangle (R := ULift.{v} A)) _ _ hone hcurry)

/-- **The biduality criterion of [stacks 0A7C] with its evaluation hypothesis discharged by
[stacks 0A69].** Only the derived homothety of [stacks 0A7B] is left as a hypothesis: the
internalized evaluation morphism at `(K, ω, ω)` is invertible because `ω` has finite injective
dimension, `RHom(ω, ω)` has finite Tor dimension, and every truncation of `K` is
pseudo-coherent — all three read at the scalar preimages. -/
public theorem isIso_dualizingBidualityMor_of_truncLE_pseudoCoherent
    (ω K : DerivedCategory (ModuleCat.{max u v} A))
    (hone : IsIso (derivedHomothety
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).toDerivedHomAdjunction
      (DerivedCategory.Q.obj (𝟙_ (Model.Complex (ULift.{v} A))))
      (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := A)).tensorUnitLeft
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω)))
    (hω : StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
      ((derivedScalarEquivalence.{u, v} A).inverse.obj ω))
    (hTor :
      let D := derivedHomAdjunction (R := ULift.{v} A)
      ∃ a b : ℤ, ∀ (N : ModuleCat.{max u v} (ULift.{v} A)) (i : ℤ), i ∉ Set.Icc a b →
        Limits.IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} (ULift.{v} A)) i).obj
          (D.tensor.obj
            (D.hom.obj
              (Opposite.op ((derivedScalarEquivalence.{u, v} A).inverse.obj ω),
                (derivedScalarEquivalence.{u, v} A).inverse.obj ω),
              (DerivedCategory.singleFunctor
                (ModuleCat.{max u v} (ULift.{v} A)) 0).obj N))))
    (hK : ∀ n : ℤ, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.TStructure.t.truncLE n).obj
        ((derivedScalarEquivalence.{u, v} A).inverse.obj K))) :
    IsIso (dualizingBidualityMor.{u, v} A ω K) :=
  isIso_dualizingBidualityMor_of_ulift A ω K hone
    (isIso_internalCurryMor_of_truncLE_pseudoCoherent _ _ _ hω hω hTor hK)

end OverRing

end Dualizing


end
