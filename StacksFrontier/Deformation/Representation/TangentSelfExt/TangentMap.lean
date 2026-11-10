module

public import StacksFrontier.Deformation.Representation.TangentSelfExt.AssociatedExtensions

/-!
# The map from the tangent space to self-extensions

The map `Deformation.tangentSelfExt` from the tangent space of the deformation category to
the first self-extension space, its bijectivity, and the comparison of pair extensions with
self-extensions used to prove its additivity.
-/

@[expose] public noncomputable section

open CategoryTheory
open Deformation

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

universe u w m

namespace Deformation

attribute [local instance] coefficientOppositeModule

attribute [local instance] coefficientCentralScalar

-- The deformation category of a representation is spelled through
-- `deformationCategoryProjection` and `squareZeroExtensionRestriction`, and the module over the
-- monoid algebra through `Rep.toModuleMonoidAlgebra`, so the `Module` and `IsHomLift` instance
-- arguments of a goal about them are only found after unfolding those heads.
attribute [local implicit_reducible] Rep.equivalenceModuleMonoidAlgebra
  Rep.toModuleMonoidAlgebra deformationCategoryProjection representationProjection
  squareZeroExtensionRestriction

/-- An equivariant linear equivalence of finite projective representations over one
coefficient algebra is an isomorphism of the representation category. -/
noncomputable def representationIsoOfLinearEquiv
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (A : Deformation.ArtinianLocalAlgCat.{u, w, w} Λ k)
    {U W : Type m} [AddCommGroup U] [Module A U] [Module.Finite A U]
    [Module.Projective A U] [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Projective A W]
    (ρU : Representation A Γ U) (ρW : Representation A Γ W)
    (e : U ≃ₗ[A] W) (he : ∀ γ z, e (ρU γ z) = ρW γ (e z)) :
    (show Deformation.RepresentationCategory Λ k Γ from
      { base := A, carrier := U, action := ρU }) ≅
    (show Deformation.RepresentationCategory Λ k Γ from
      { base := A, carrier := W, action := ρW }) where
  hom :=
    { base := 𝟙 A
      map := e.toLinearMap.toAddMonoidHom
      map_smul := e.map_smul
      equivariant := he
      isBaseChange := IsBaseChange.ofEquiv e }
  inv :=
    { base := 𝟙 A
      map := e.symm.toLinearMap.toAddMonoidHom
      map_smul := e.symm.map_smul
      equivariant := fun γ z ↦ by
        apply e.injective
        change e (e.symm (ρW γ z)) = e (ρU γ (e.symm z))
        rw [e.apply_symm_apply, he, e.apply_symm_apply]
      isBaseChange := IsBaseChange.ofEquiv e.symm }
  hom_inv_id := by
    apply Deformation.RepresentationCategory.Hom.ext
    · rfl
    · ext z
      exact e.symm_apply_apply z
  inv_hom_id := by
    apply Deformation.RepresentationCategory.Hom.ext
    · rfl
    · ext z
      exact e.apply_symm_apply z

/-- Two deformations with the same associated self-extension are isomorphic in the fibre
over the dual numbers. -/
theorem nonempty_iso_of_associatedSelfExtension
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    {M : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    (hx : IsAssociatedSelfExtension V ρ₀ x M f g)
    (hy : IsAssociatedSelfExtension V ρ₀ y M f g) : Nonempty (x ≅ y) := by
  rcases x with ⟨⟨X, ⟨⟨⟩⟩, α⟩, hxbase⟩
  rcases y with ⟨⟨Y, ⟨⟨⟩⟩, β⟩, hybase⟩
  rcases X with @⟨A, U, hU, hmodU, hfinU, hprojU, ρU⟩
  rcases Y with @⟨B, W, hW, hmodW, hfinW, hprojW, ρW⟩
  change A = Deformation.augmentedDualNumbers at hxbase
  change B = Deformation.augmentedDualNumbers at hybase
  cases hxbase
  cases hybase
  let : Module (DualNumber k) U := hmodU
  let : Module (DualNumber k) W := hmodW
  let : Module.Finite (DualNumber k) U := hfinU
  let : Module.Finite (DualNumber k) W := hfinW
  let : Module.Projective (DualNumber k) U := hprojU
  let : Module.Projective (DualNumber k) W := hprojW
  obtain ⟨e, he₁, heΓ, heq, heε⟩ := hx
  obtain ⟨e', he₁', heΓ', heq', heε'⟩ := hy
  let a : U ≃+ W := e.symm.trans e'
  have ha (z : M) : a (e z) = e' z := by simp [a]
  have ha₁ (c : k) (z : U) :
      a ((TrivSqZeroExt.inl c : DualNumber k) • z) =
        (TrivSqZeroExt.inl c : DualNumber k) • a z := by
    obtain ⟨z, rfl⟩ := e.surjective z
    -- the scalar of `IsAssociatedSelfExtension` is transported along the base equality, so
    -- it is only definitionally `TrivSqZeroExt.inl c`; the chain is built in term mode.
    exact (congrArg a (he₁ c z).symm).trans ((ha _).trans ((he₁' c z).trans
      (congrArg (fun w ↦ (TrivSqZeroExt.inl c : DualNumber k) • w) (ha z)).symm))
  have haε (z : U) : a ((DualNumber.eps : DualNumber k) • z) =
      (DualNumber.eps : DualNumber k) • a z := by
    obtain ⟨z, rfl⟩ := e.surjective z
    exact (congrArg a (heε z).symm).trans ((ha _).trans ((heε' z).trans
      (congrArg (fun w ↦ (DualNumber.eps : DualNumber k) • w) (ha z)).symm))
  let l : U ≃ₗ[DualNumber k] W :=
    { a with
      map_smul' := fun r z ↦ by
        have hr : r = TrivSqZeroExt.inl r.fst +
            TrivSqZeroExt.inl r.snd * (DualNumber.eps : DualNumber k) := by
          apply TrivSqZeroExt.ext <;>
            simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
              TrivSqZeroExt.fst_mul, dualNumber_snd_mul,
              TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
              DualNumber.fst_eps, DualNumber.snd_eps,
              mul_zero, mul_one, add_zero, zero_add]
        change a (r • z) = r • a z
        conv_lhs => rw [hr]
        conv_rhs => rw [hr]
        rw [add_smul, add_smul, map_add, mul_smul, mul_smul, ha₁, ha₁, haε] }
  have hlΓ (γ : Γ) (z : U) : l (ρU γ z) = ρW γ (l z) := by
    obtain ⟨z, rfl⟩ := e.surjective z
    change a (ρU γ (e z)) = ρW γ (a (e z))
    rw [← heΓ, ha, heΓ', ha]
  have hlq (z : U) : β.map (l z) = α.map z := by
    obtain ⟨z, rfl⟩ := e.surjective z
    change β.map (a (e z)) = α.map (e z)
    rw [ha]
    exact (heq' z).symm.trans (heq z)
  let j := representationIsoOfLinearEquiv Deformation.augmentedDualNumbers ρU ρW l hlΓ
  have hjq : j.hom ≫ β = α := by
    apply Deformation.RepresentationCategory.Hom.ext
    · ext r
      exact (dualNumbers_to_specialFiberBase_apply β.base r).trans
        (dualNumbers_to_specialFiberBase_apply α.base r).symm
    · ext z
      exact hlq z
  let i : Over.mk α ≅ Over.mk β := Over.isoMk j hjq
  refine ⟨{
    hom := ⟨i.hom, ?_⟩
    inv := ⟨i.inv, ?_⟩
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · exact IsHomLift.of_fac _ _ _ rfl rfl (by simp [i, j, deformationCategoryProjection,
      representationProjection, representationIsoOfLinearEquiv])
  · exact IsHomLift.of_fac _ _ _ rfl rfl (by simp [i, j, deformationCategoryProjection,
      representationProjection, representationIsoOfLinearEquiv])
  · exact Subtype.ext i.hom_inv_id
  · exact Subtype.ext i.inv_hom_id

/-- Being the self-extension associated to a deformation is transported along an
isomorphism of short exact sequences fixing the quotient. -/
theorem associatedSelfExtension_of_extensionIso
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)))
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M'}
    {g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    (i : M ≅ M') (hi : f ≫ i.hom = f') (hg : i.hom ≫ g' = g)
    (hx : IsAssociatedSelfExtension V ρ₀ x M' f' g') :
    IsAssociatedSelfExtension V ρ₀ x M f g := by
  obtain ⟨e, he₁, heΓ, heq, heε⟩ := hx
  let l := i.toLinearEquiv
  have hl (v) : l (f.hom v) = f'.hom v := congrArg (fun q ↦ q.hom v) hi
  have hq (z) : g'.hom (l z) = g.hom z := congrArg (fun q ↦ q.hom z) hg
  refine ⟨l.toAddEquiv.trans e, ?_, ?_, ?_, ?_⟩
  · intro a z
    exact (congrArg e (l.map_smul _ z)).trans (he₁ a (l z))
  · intro γ z
    exact (congrArg e (l.map_smul _ z)).trans (heΓ γ (l z))
  · intro z
    exact (hq z).symm.trans (heq (l z))
  · intro z
    change e (l (f.hom (g.hom z))) = _
    rw [hl, ← hq]
    exact heε (l z)

/-- Being the self-extension associated to a deformation depends only on the isomorphism
class of the deformation. -/
theorem associatedSelfExtension_of_iso
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (i : x ≅ y)
    {M : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    (hx : IsAssociatedSelfExtension V ρ₀ x M f g) :
    IsAssociatedSelfExtension V ρ₀ y M f g := by
  rcases x with ⟨⟨X, ⟨⟨⟩⟩, α⟩, hxbase⟩
  rcases y with ⟨⟨Y, ⟨⟨⟩⟩, β⟩, hybase⟩
  rcases X with @⟨A, U, hU, hmodU, hfinU, hprojU, ρU⟩
  rcases Y with @⟨B, W, hW, hmodW, hfinW, hprojW, ρW⟩
  change A = Deformation.augmentedDualNumbers at hxbase
  change B = Deformation.augmentedDualNumbers at hybase
  cases hxbase
  cases hybase
  let : Module (DualNumber k) U := hmodU
  let : Module (DualNumber k) W := hmodW
  let a := i.hom.1.left
  let b := i.inv.1.left
  have hab (z : U) : b.map (a.map z) = z :=
    congrArg (fun q ↦ q.1.left.map z) i.hom_inv_id
  have hba (z : W) : a.map (b.map z) = z :=
    congrArg (fun q ↦ q.1.left.map z) i.inv_hom_id
  let eUW : U ≃+ W :=
    { a.map with invFun := b.map, left_inv := hab, right_inv := hba }
  have habase : a.base = 𝟙 _ := by
    have := i.hom.2
    have h := IsHomLift.fac (deformationCategoryProjection (Λ := Λ) V ρ₀)
      (𝟙 (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))) i.hom.1
    simpa [a, deformationCategoryProjection, representationProjection] using h.symm
  have hasmul (r : DualNumber k) (z : U) : a.map (r • z) = r • a.map z := by
    have h := a.map_smul r z
    rw [habase] at h
    exact h
  obtain ⟨e, he₁, heΓ, heq, heε⟩ := hx
  refine ⟨e.trans eUW, ?_, ?_, ?_, ?_⟩
  · intro c z
    exact (congrArg a.map (he₁ c z)).trans (hasmul _ _)
  · intro γ z
    exact (congrArg a.map (heΓ γ z)).trans (a.equivariant γ _)
  · intro z
    have h := congrArg (fun q ↦ q.map (e z)) i.hom.1.w
    exact (heq z).trans h.symm
  · intro z
    exact (congrArg a.map (heε z)).trans (hasmul _ _)

/-- A deformation over the dual numbers determines a single extension class, shared by
every self-extension associated to it. -/
theorem exists_selfExtClass_of_deformation
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))) :
    let M₀ := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)
    ∃ ξ : Abelian.Ext M₀ M₀ 1,
      ∀ (M : ModuleCat (MonoidAlgebra k Γ)) (f : M₀ ⟶ M) (g : M ⟶ M₀)
        (hfg : f ≫ g = 0) (h : (ShortComplex.mk f g hfg).ShortExact),
        IsAssociatedSelfExtension V ρ₀ x M f g → ξ = h.extClass := by
  obtain ⟨M, f, g, hfg, h, hx⟩ := exists_associatedSelfExtension V ρ₀ x
  refine ⟨h.extClass, fun M' f' g' hfg' h' hx' ↦ ?_⟩
  exact associatedSelfExtension_extClass_eq V ρ₀ x h h' hx hx'

/-- An additive map between modules over a monoid algebra that commutes with the scalars
`single 1 c` and `single γ 1` is linear. -/
private theorem map_smul_monoidAlgebra_of_single
    {k : Type w} {Γ : Type*} [Field k] [Group Γ]
    {M M' : Type*} [AddCommGroup M] [Module (MonoidAlgebra k Γ) M]
    [AddCommGroup M'] [Module (MonoidAlgebra k Γ) M'] (l : M →+ M')
    (hk : ∀ (c : k) (z : M), l ((MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • z) =
      (MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • l z)
    (hΓ : ∀ (γ : Γ) (z : M), l ((MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • z) =
      (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • l z)
    (r : MonoidAlgebra k Γ) (z : M) : l (r • z) = r • l z := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp only [zero_smul, map_zero]
  | add r s hr hs => simp only [add_smul, map_add, hr, hs]
  | single γ c =>
    rw [show MonoidAlgebra.single γ c =
        (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) *
          MonoidAlgebra.single 1 c by simp, mul_smul, hΓ, hk, mul_smul]

/-- A morphism of deformations lying over multiplication by a scalar on the dual numbers
scales the extension class by that scalar. -/
theorem associatedSelfExtension_extClass_smul_of_hom
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (a : k) (b : x.1 ⟶ y.1)
    (hb₁ : let hxbase : x.1.left.base = Deformation.augmentedDualNumbers := x.2
      let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
      ∀ c : k, b.left.base.hom (hxbase.symm ▸ (TrivSqZeroExt.inl c : DualNumber k)) =
        hybase.symm ▸ (TrivSqZeroExt.inl c : DualNumber k))
    (hbε : let hxbase : x.1.left.base = Deformation.augmentedDualNumbers := x.2
      let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
      b.left.base.hom (hxbase.symm ▸ (DualNumber.eps : DualNumber k)) =
        (hybase.symm ▸ (TrivSqZeroExt.inl a : DualNumber k)) *
          (hybase.symm ▸ (DualNumber.eps : DualNumber k)))
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M'}
    {g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {hfg : f ≫ g = 0} {hfg' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (h' : (ShortComplex.mk f' g' hfg').ShortExact)
    (hx : IsAssociatedSelfExtension V ρ₀ x M f g)
    (hy : IsAssociatedSelfExtension V ρ₀ y M' f' g') :
    h'.extClass = a • h.extClass := by
  rcases x with ⟨⟨X, ⟨⟨⟩⟩, α⟩, hxbase⟩
  rcases y with ⟨⟨Y, ⟨⟨⟩⟩, β⟩, hybase⟩
  rcases X with @⟨A, U, hU, hmodU, hfinU, hprojU, ρU⟩
  rcases Y with @⟨B, W, hW, hmodW, hfinW, hprojW, ρW⟩
  change A = Deformation.augmentedDualNumbers at hxbase
  change B = Deformation.augmentedDualNumbers at hybase
  cases hxbase
  cases hybase
  let : Module (DualNumber k) U := hmodU
  let : Module (DualNumber k) W := hmodW
  obtain ⟨e, he₁, heΓ, heq, heε⟩ := hx
  obtain ⟨e', he₁', heΓ', heq', heε'⟩ := hy
  let l : M →+ M' := e'.symm.toAddMonoidHom.comp
    (b.left.map.comp e.toAddMonoidHom)
  have hl (z : M) : e' (l z) = b.left.map (e z) := e'.apply_symm_apply _
  have hl₁ (c : k) (z : M) :
      l ((MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single 1 c : MonoidAlgebra k Γ) • l z := by
    apply e'.injective
    rw [hl, he₁, b.left.map_smul, hb₁, he₁', hl]
  have hlΓ (γ : Γ) (z : M) :
      l ((MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • l z := by
    apply e'.injective
    rw [hl, heΓ, b.left.equivariant, heΓ', hl]
  let lR : M →ₗ[MonoidAlgebra k Γ] M' :=
    { l with map_smul' := map_smul_monoidAlgebra_of_single l hl₁ hlΓ }
  have hq (z : M) : g'.hom (lR z) = g.hom z := by
    rw [heq', heq]
    change β.map (e' (l z)) = α.map (e z)
    rw [hl]
    exact congrArg (fun q ↦ q.map (e z)) b.w
  have hi : f ≫ ModuleCat.ofHom lR = (a • 𝟙 _) ≫ f' := by
    ext v
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective g).1 h.epi_g v
    apply e'.injective
    change e' (l (f.hom (g.hom z))) =
      e' (f'.hom ((MonoidAlgebra.single 1 a : MonoidAlgebra k Γ) • g.hom z))
    rw [hl, heε, b.left.map_smul, hbε, mul_smul]
    rw [show f'.hom ((MonoidAlgebra.single 1 a : MonoidAlgebra k Γ) • g.hom z) =
        (MonoidAlgebra.single 1 a : MonoidAlgebra k Γ) • f'.hom (g.hom z) from
      f'.hom.map_smul (MonoidAlgebra.single 1 a) _]
    rw [he₁', ← hq, heε']
    exact congrArg (fun z ↦ (TrivSqZeroExt.inl a : DualNumber k) •
      (DualNumber.eps : DualNumber k) • z) (hl z).symm
  have hn := h.extClass_naturality h'
    ({
      τ₁ := a • 𝟙 _
      τ₂ := ModuleCat.ofHom lR
      τ₃ := 𝟙 _
      comm₁₂ := hi.symm
      comm₂₃ := by ext z; exact hq z } :
      ShortComplex.mk f g hfg ⟶ ShortComplex.mk f' g' hfg')
  simpa only [Abelian.Ext.mk₀_id_comp, ← Abelian.Ext.smul_eq_comp_mk₀] using hn.symm

/-- The map from the tangent space of the deformation category of `ρ₀` to the first
self-extension group, sending a deformation to the class of its associated extension. -/
noncomputable def tangentSelfExt
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : Deformation.IsCofiberedInGroupoids
      (deformationCategoryProjection (Λ := Λ) V ρ₀))
    (t : Deformation.artinianTangentSpace Λ k
      (Deformation.isomorphismClasses
        (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)) h)) :
    let M₀ := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)
    Abelian.Ext M₀ M₀ 1 :=
  Classical.choose (exists_selfExtClass_of_deformation V ρ₀
    (Classical.choose (Deformation.classOf_surjective _ h _ t)))

/-- The value of `tangentSelfExt` on the class of a deformation is the extension class of
any associated self-extension. -/
theorem tangentSelfExt_classOf
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : Deformation.IsCofiberedInGroupoids
      (deformationCategoryProjection (Λ := Λ) V ρ₀))
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k)))
    (M : ModuleCat (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀))
    (hfg : f ≫ g = 0) (hexact : (ShortComplex.mk f g hfg).ShortExact)
    (hx : IsAssociatedSelfExtension V ρ₀ x M f g) :
    tangentSelfExt V ρ₀ h (Deformation.classOf _ h x) = hexact.extClass := by
  let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
  let y := Classical.choose (Deformation.classOf_surjective 𝓕 h _
    (Deformation.classOf 𝓕 h x))
  have hy : Deformation.classOf 𝓕 h y = Deformation.classOf 𝓕 h x :=
    Classical.choose_spec (Deformation.classOf_surjective 𝓕 h _ _)
  have hi : Nonempty (y ≅ x) := Quotient.exact
    ((Deformation.classOf_eq 𝓕 h y).symm.trans
      ((congrArg (cast (Deformation.isomorphismClasses_obj 𝓕 h _)) hy).trans
        (Deformation.classOf_eq 𝓕 h x)))
  exact Classical.choose_spec (exists_selfExtClass_of_deformation V ρ₀ y)
    M f g hfg hexact (associatedSelfExtension_of_iso V ρ₀ hi.some.symm hx)

/-- Every self-extension class of `ρ₀` comes from a deformation. -/
theorem tangentSelfExt_surjective
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : Deformation.IsCofiberedInGroupoids
      (deformationCategoryProjection (Λ := Λ) V ρ₀)) :
    Function.Surjective (tangentSelfExt V ρ₀ h) := by
  intro ξ
  obtain ⟨M, f, g, hfg, hexact, rfl⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).1 ξ
  obtain ⟨x, hx⟩ := exists_deformation_of_selfExtension (Λ := Λ) V ρ₀ M f g hfg hexact
  exact ⟨Deformation.classOf _ h x, tangentSelfExt_classOf V ρ₀ h x M f g hfg hexact hx⟩

/-- Deformations with the same self-extension class are isomorphic, so `tangentSelfExt`
is injective. -/
theorem tangentSelfExt_injective
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (h : Deformation.IsCofiberedInGroupoids
      (deformationCategoryProjection (Λ := Λ) V ρ₀)) :
    Function.Injective (tangentSelfExt V ρ₀ h) := by
  intro s t hst
  let 𝓕 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
  obtain ⟨x, rfl⟩ := Deformation.classOf_surjective 𝓕 h _ s
  obtain ⟨y, rfl⟩ := Deformation.classOf_surjective 𝓕 h _ t
  obtain ⟨M, f, g, hfg, hexact, hx⟩ := exists_associatedSelfExtension V ρ₀ x
  obtain ⟨M', f', g', hfg', hexact', hy⟩ := exists_associatedSelfExtension V ρ₀ y
  rw [tangentSelfExt_classOf V ρ₀ h x M f g hfg hexact hx,
    tangentSelfExt_classOf V ρ₀ h y M' f' g' hfg' hexact' hy] at hst
  obtain ⟨i, hi, hg⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum _ _ _).2.1
      _ _ _ _ _ _ _ _ hexact hexact' |>.1 hst
  have hy' := associatedSelfExtension_of_extensionIso V ρ₀ y i hi hg hy
  have hxy := nonempty_iso_of_associatedSelfExtension V ρ₀ hx hy'
  exact (Equiv.cast (Deformation.isomorphismClasses_obj 𝓕 h _)).injective
    ((Deformation.classOf_eq 𝓕 h x).trans
      ((Quotient.sound hxy).trans (Deformation.classOf_eq 𝓕 h y).symm))

/-- A morphism of short exact sequences that is the identity on the quotient expresses the
extension class of the target as the pushforward of that of the source. -/
private theorem extClass_eq_comp_of_tau₃_eq_id
    {C : Type*} [Category C] [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact)
    {A M : C} {f : A ⟶ M} {g : M ⟶ S.X₃} {w : f ≫ g = 0}
    (hT : (ShortComplex.mk f g w).ShortExact) (a : S ⟶ ShortComplex.mk f g w)
    (ha : a.τ₃ = 𝟙 S.X₃) :
    hS.extClass.comp (Abelian.Ext.mk₀ a.τ₁) (add_zero 1) = hT.extClass := by
  have h := hS.extClass_naturality hT a
  rwa [ha, Abelian.Ext.mk₀_id_comp] at h

/-- Three extensions of a common object, compared with a fixed short exact sequence by
maps that are the identity on the quotient, have additive extension classes when the
comparison maps are additive on the sub-object. -/
theorem extClass_eq_add_of_common_extension
    {C : Type*} [Category C] [Abelian C] [HasExt C]
    (S : ShortComplex C) (hS : S.ShortExact)
    {A M₁ M₂ M₃ : C}
    (f₁ : A ⟶ M₁) (g₁ : M₁ ⟶ S.X₃) (w₁ : f₁ ≫ g₁ = 0)
    (f₂ : A ⟶ M₂) (g₂ : M₂ ⟶ S.X₃) (w₂ : f₂ ≫ g₂ = 0)
    (f₃ : A ⟶ M₃) (g₃ : M₃ ⟶ S.X₃) (w₃ : f₃ ≫ g₃ = 0)
    (h₁ : (ShortComplex.mk f₁ g₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk f₂ g₂ w₂).ShortExact)
    (h₃ : (ShortComplex.mk f₃ g₃ w₃).ShortExact)
    (a₁ : S ⟶ ShortComplex.mk f₁ g₁ w₁)
    (a₂ : S ⟶ ShortComplex.mk f₂ g₂ w₂)
    (a₃ : S ⟶ ShortComplex.mk f₃ g₃ w₃)
    (ha₁ : a₁.τ₃ = 𝟙 S.X₃) (ha₂ : a₂.τ₃ = 𝟙 S.X₃)
    (ha₃ : a₃.τ₃ = 𝟙 S.X₃) (ha : a₃.τ₁ = a₁.τ₁ + a₂.τ₁) :
    h₃.extClass = h₁.extClass + h₂.extClass := by
  rw [← extClass_eq_comp_of_tau₃_eq_id hS h₃ a₃ ha₃, ← extClass_eq_comp_of_tau₃_eq_id hS h₁ a₁ ha₁,
    ← extClass_eq_comp_of_tau₃_eq_id hS h₂ a₂ ha₂, ha, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- The map from the twofold product of a representation to the representation itself
given by a linear combination of the two coordinates. -/
def pairCoefficientHom
    {k : Type w} {Γ : Type*} [Field k] [Group Γ]
    {V : Type m} [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V) (a b : k) :
    Rep.of (ρ₀.prod ρ₀) ⟶ Rep.of ρ₀ :=
  Rep.ofHom {
    __ := a • LinearMap.fst k V V + b • LinearMap.snd k V V
    isIntertwining' := fun γ ↦ by
      apply LinearMap.ext
      intro v
      change a • ρ₀ γ v.1 + b • ρ₀ γ v.2 =
        ρ₀ γ (a • v.1 + b • v.2)
      rw [map_add, map_smul, map_smul] }

/-- The coordinate formula for `pairCoefficientHom`. -/
theorem pairCoefficientHom_apply
    {k : Type w} {Γ : Type*} [Field k] [Group Γ]
    {V : Type m} [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V) (a b : k) (v : V × V) :
    (pairCoefficientHom ρ₀ a b).hom v = a • v.1 + b • v.2 := rfl

/-- The diagonal combination of `pairCoefficientHom` is the sum of the two projections. -/
theorem pairCoefficientHom_add
    {k : Type w} {Γ : Type*} [Field k] [Group Γ]
    {V : Type m} [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V) :
    pairCoefficientHom ρ₀ 1 1 =
      pairCoefficientHom ρ₀ 1 0 + pairCoefficientHom ρ₀ 0 1 := by
  ext v <;> simp [Rep.add_hom, pairCoefficientHom]

/-- A pair extension and a self-extension related by a map collapsing the two coordinate
radicals by prescribed scalars are compared by a morphism of short complexes that is
the identity on the quotient. -/
theorem pairShortComplexHom
    {k : Type w} {Γ : Type*} [Field k] [Group Γ]
    {V : Type m} [AddCommGroup V] [Module k V]
    (ρ₀ : Representation k Γ V)
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of (ρ₀.prod ρ₀)) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)) (hfg : f ≫ g = 0)
    (f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M')
    (g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)) (hfg' : f' ≫ g' = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (l : M ⟶ M') (hlg : l ≫ g' = g) (a b : k)
    (h₁ : ∀ z : M, l.hom (f.hom (g.hom z, 0)) =
      f'.hom ((MonoidAlgebra.single 1 a : MonoidAlgebra k Γ) • g.hom z))
    (h₂ : ∀ z : M, l.hom (f.hom (0, g.hom z)) =
      f'.hom ((MonoidAlgebra.single 1 b : MonoidAlgebra k Γ) • g.hom z)) :
    ∃ q : ShortComplex.mk f g hfg ⟶ ShortComplex.mk f' g' hfg',
      q.τ₁ = (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map
        (pairCoefficientHom ρ₀ a b) ∧ q.τ₃ = 𝟙 _ := by
  let Q := (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map
    (pairCoefficientHom ρ₀ a b)
  have hscalar (d : k) (v : V) :
      (MonoidAlgebra.single 1 d : MonoidAlgebra k Γ) •
        (show ρ₀.asModule from v) = (show ρ₀.asModule from d • v) := by
    change (ρ₀.asAlgebraHom (MonoidAlgebra.single 1 d)) v = d • v
    simp
  have hi : f ≫ l = Q ≫ f' := by
    ext v
    rcases v with ⟨v₁, v₂⟩
    obtain ⟨z₁, rfl⟩ := (ModuleCat.epi_iff_surjective g).1 h.epi_g v₁
    obtain ⟨z₂, rfl⟩ := (ModuleCat.epi_iff_surjective g).1 h.epi_g v₂
    change l.hom (f.hom (g.hom z₁, g.hom z₂)) =
      f'.hom (Q.hom (g.hom z₁, g.hom z₂))
    have hQ : Q.hom (g.hom z₁, g.hom z₂) =
        (MonoidAlgebra.single 1 a : MonoidAlgebra k Γ) • g.hom z₁ +
          (MonoidAlgebra.single 1 b : MonoidAlgebra k Γ) • g.hom z₂ := by
      change (a • (show V from g.hom z₁) : V) +
        (b • (show V from g.hom z₂) : V) = _
      exact congrArg₂ (· + ·) (hscalar a (show V from g.hom z₁)).symm
        (hscalar b (show V from g.hom z₂)).symm
    rw [hQ]
    have hp : ((g.hom z₁, g.hom z₂) : V × V) =
        (g.hom z₁, (0 : V)) + (0, g.hom z₂) := by
      change (g.hom z₁, g.hom z₂) = (g.hom z₁ + 0, 0 + g.hom z₂)
      simp
    have hpf : f.hom (g.hom z₁, g.hom z₂) =
        f.hom (g.hom z₁, 0) + f.hom (0, g.hom z₂) := by
      convert f.hom.map_add (g.hom z₁, 0) (0, g.hom z₂) using 1
      exact congrArg f.hom hp
    rw [hpf, l.hom.map_add, f'.hom.map_add, h₁, h₂]
  refine ⟨{
    τ₁ := Q
    τ₂ := l
    τ₃ := 𝟙 _
    comm₁₂ := hi.symm
    comm₂₃ := by simpa using hlg }, rfl, rfl⟩

/-- The comparison morphism of `pairShortComplexHom` for the extensions associated to a
deformation over the rank-two square-zero extension. -/
theorem associatedPairExtension_shortComplexHom
    {Λ : Type u} {k : Type w} {Γ : Type*}
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    (V : Type m) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    {x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      ((Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
        (FGModuleCat.of k (k × k)))}
    {y : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (Deformation.augmentedDualNumbers (Λ := Λ) (k := k))}
    (a c : k) (b : x.1 ⟶ y.1)
    (hb₁ : let hxbase : (x.1.left.base =
        (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k (k × k))) := x.2
      let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
      ∀ d : k, b.left.base.hom (hxbase.symm ▸
        (TrivSqZeroExt.inl d : TrivSqZeroExt k (k × k))) =
        hybase.symm ▸ (TrivSqZeroExt.inl d : DualNumber k))
    (hbε₁ : let hxbase : (x.1.left.base =
        (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k (k × k))) := x.2
      let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
      b.left.base.hom (hxbase.symm ▸
        (TrivSqZeroExt.inr (1, 0) : TrivSqZeroExt k (k × k))) =
        (hybase.symm ▸ (TrivSqZeroExt.inl a : DualNumber k)) *
          (hybase.symm ▸ (DualNumber.eps : DualNumber k)))
    (hbε₂ : let hxbase : (x.1.left.base =
        (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
          (FGModuleCat.of k (k × k))) := x.2
      let hybase : y.1.left.base = Deformation.augmentedDualNumbers := y.2
      b.left.base.hom (hxbase.symm ▸
        (TrivSqZeroExt.inr (0, 1) : TrivSqZeroExt k (k × k))) =
        (hybase.symm ▸ (TrivSqZeroExt.inl c : DualNumber k)) *
          (hybase.symm ▸ (DualNumber.eps : DualNumber k)))
    {M M' : ModuleCat (MonoidAlgebra k Γ)}
    {f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of (ρ₀.prod ρ₀)) ⟶ M}
    {g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {f' : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀) ⟶ M'}
    {g' : M' ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj
      (Rep.of ρ₀)}
    {hfg : f ≫ g = 0} {hfg' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f g hfg).ShortExact)
    (hx : IsAssociatedPairExtension V ρ₀ x M f g)
    (hy : IsAssociatedSelfExtension V ρ₀ y M' f' g') :
    ∃ q : ShortComplex.mk f g hfg ⟶ ShortComplex.mk f' g' hfg',
      q.τ₁ = (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.map
        (pairCoefficientHom ρ₀ a c) ∧ q.τ₃ = 𝟙 _ := by
  rcases x with ⟨⟨X, ⟨⟨⟩⟩, α⟩, hxbase⟩
  rcases y with ⟨⟨Y, ⟨⟨⟩⟩, β⟩, hybase⟩
  rcases X with @⟨A, U, hU, hmodU, hfinU, hprojU, ρU⟩
  rcases Y with @⟨B, W, hW, hmodW, hfinW, hprojW, ρW⟩
  change A = (Deformation.artinianSquareZeroExtensionFunctor Λ k).obj
    (FGModuleCat.of k (k × k)) at hxbase
  change B = Deformation.augmentedDualNumbers at hybase
  cases hxbase
  cases hybase
  let : Module (TrivSqZeroExt k (k × k)) U := hmodU
  let : Module (DualNumber k) W := hmodW
  obtain ⟨e, he₁, heΓ, heq, heε₁, heε₂⟩ := hx
  obtain ⟨e', he₁', heΓ', heq', heε'⟩ := hy
  let l : M →+ M' := e'.symm.toAddMonoidHom.comp
    (b.left.map.comp e.toAddMonoidHom)
  have hl (z : M) : e' (l z) = b.left.map (e z) := e'.apply_symm_apply _
  have hl₁ (d : k) (z : M) :
      l ((MonoidAlgebra.single 1 d : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single 1 d : MonoidAlgebra k Γ) • l z := by
    apply e'.injective
    rw [hl, he₁, b.left.map_smul, hb₁, he₁', hl]
  have hlΓ (γ : Γ) (z : M) :
      l ((MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • z) =
        (MonoidAlgebra.single γ 1 : MonoidAlgebra k Γ) • l z := by
    apply e'.injective
    rw [hl, heΓ, b.left.equivariant, heΓ', hl]
  let lR : M →ₗ[MonoidAlgebra k Γ] M' :=
    { l with map_smul' := map_smul_monoidAlgebra_of_single l hl₁ hlΓ }
  have hq (z : M) : g'.hom (lR z) = g.hom z := by
    rw [heq', heq]
    change β.map (e' (l z)) = α.map (e z)
    rw [hl]
    exact congrArg (fun q ↦ q.map (e z)) b.w
  have key (d : k) (z : M) (p : V × V)
      (u : (artinianSquareZeroExtensionFunctor Λ k).obj (FGModuleCat.of k (k × k)))
      (hu : e (f.hom p) = u • e z)
      (hbu : b.left.base.hom u = (TrivSqZeroExt.inl d : DualNumber k) * DualNumber.eps) :
      lR (f.hom p) = f'.hom ((MonoidAlgebra.single 1 d : MonoidAlgebra k Γ) • g.hom z) := by
    apply e'.injective
    change e' (l (f.hom p)) =
      e' (f'.hom ((MonoidAlgebra.single 1 d : MonoidAlgebra k Γ) • g.hom z))
    rw [hl, hu, b.left.map_smul, hbu]
    erw [mul_smul]
    rw [map_smul, he₁', ← hq, heε']
    exact congrArg (fun z ↦ (TrivSqZeroExt.inl d : DualNumber k) •
      (DualNumber.eps : DualNumber k) • z) (hl z).symm
  have h₁ (z : M) := key a z (g.hom z, 0) _ (by simpa [← heq z] using heε₁ z) hbε₁
  have h₂ (z : M) := key c z (0, g.hom z) _ (by simpa [← heq z] using heε₂ z) hbε₂
  exact pairShortComplexHom ρ₀ f g hfg f' g' hfg' h (ModuleCat.ofHom lR)
    (by ext z; exact hq z) a c h₁ h₂

end Deformation
