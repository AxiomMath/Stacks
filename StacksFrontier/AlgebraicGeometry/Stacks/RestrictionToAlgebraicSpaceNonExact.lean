module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatObjectConservativity
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeChartAsAlgebraicSpaceChart
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BigSiteNotExact
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet

/-!
# The functor `d` of Stacks 0GQS is not exact in general

Item (4) of Stacks 0GQS says that the functor

```
d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),   ℱ ↦ f^*ℱ|_{U_étale},
```

attached to a 1-morphism `f : 𝒰 ⟶ 𝒳` from the algebraic stack of an algebraic space `U`, is right
exact but not exact in general; the source omits an example showing non-exactness.  Right
exactness is `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteColimits_qcohSpaceRestriction`.
This file gives the example.

Take `𝒳` the algebraic stack of the scheme `Spec(ℤ)` over `S = Spec(ℤ)`, `U = Spec(𝔽₂)` and `f`
the 1-morphism induced by the closed immersion `Spec(𝔽₂) ⟶ Spec(ℤ)`.  Multiplication by `2` on
`𝒪_𝒳` is a monomorphism of `QCoh(𝒪_𝒳)`: on sections over a flat object `T ⟶ Spec(ℤ)` it is
multiplication by `2` on `Γ(T, 𝒪_T)`, which is injective because every local ring of `T` is flat
over a local ring of `Spec(ℤ)`, a domain of characteristic zero; and a map out of a quasi-coherent
module is determined by its values on the flat objects
(`AlgebraicGeometry.Stack.hom_ext_of_isQuasicoherentOnSite_of_flat`).  But `d` of it is
multiplication by `2` on `d(𝒪_𝒳)`, whose sections over every étale chart `W` of `U` are the ring
`Γ(W, 𝒪_W)` of characteristic `2`; so `d(2)` is zero, while `d(𝒪_𝒳)` is not, its sections over the
identity chart being `𝔽₂`.  A functor preserving finite limits preserves monomorphisms, and a
monomorphism `m` with `m ≫ m = m` would be the identity.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.mono_of_injective_app_flatObject`: a map of
  quasi-coherent modules on an algebraic stack which is injective on sections over every flat
  object is a monomorphism of `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.QcohSpaceRestrictionNonExact.mono_twoQcoh`:
  multiplication by `2` on `𝒪_𝒳` is a monomorphism of `QCoh(𝒪_𝒳)`, for `𝒳` the stack of
  `Spec(ℤ)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.QcohSpaceRestrictionNonExact.not_mono_map_twoQcoh`:
  its image under `d` is not a monomorphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.not_preservesFiniteLimits_qcohSpaceRestriction_of_site`:
  **Stacks 0GQS, item (4), non-exactness**, on every big fppf site.
* `AlgebraicGeometry.Stack.AlgebraicStacks.not_preservesFiniteLimits_qcohSpaceRestriction`:
  the same, as an existential statement over all the data.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

/-! ### Monomorphisms of quasi-coherent modules are detected on flat objects -/

section Mono

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **A map of quasi-coherent modules injective over the flat objects is a monomorphism.**  A map
`φ : F ⟶ G` of `QCoh(𝒪_𝒳)` which is injective on sections over every flat object of `𝒳` is a
monomorphism of `QCoh(𝒪_𝒳)`: maps out of a quasi-coherent module are determined by their values
on flat objects. -/
theorem mono_of_injective_app_flatObject {F G : quasicoherentModules B S hS 𝒳} (φ : F ⟶ G)
    (hφ : ∀ y : 𝒳.val.val.obj, flatObject B S hS 𝒳.val y →
      Function.Injective (φ.hom.val.app (op y)).hom) : Mono φ := by
  refine ⟨fun {T} g₁ g₂ h => ObjectProperty.hom_ext _ ?_⟩
  refine hom_ext_of_isQuasicoherentOnSite_of_flat 𝒳 T.property fun y hy => ?_
  ext s
  exact hφ y hy (congrArg (fun k => (k.hom.val.app (op y)).hom s) h)

end Mono

namespace QcohSpaceRestrictionNonExact

open AssociatedModuleNotExact

/-! ### Rings of sections -/

/-- Multiplication by `2` is injective on the global sections of a scheme flat over `Spec(ℤ)`:
every local ring is flat over a local ring of `Spec(ℤ)`, a domain in which `2 ≠ 0`. -/
theorem injective_add_self_of_flat {T : Scheme.{u}} (g : T ⟶ specInt.{u}) [Flat g] :
    Function.Injective (fun x : (Γ(T, ⊤) : Type u) => x + x) := by
  have hreg : IsSMulRegular (Γ(T, ⊤) : Type u) (2 : (Γ(T, ⊤) : Type u)) := by
    refine IsSMulRegular.of_right_eq_zero_of_smul fun z hz => ?_
    refine TopCat.Presheaf.section_ext
      (⟨T.presheaf, T.IsSheaf⟩ : TopCat.Sheaf CommRingCat.{u} T.toTopCat) ⊤ z 0 fun x hx => ?_
    have h2 : (2 : specInt.{u}.presheaf.stalk (g x)) ≠ 0 := by
      intro h
      apply two_ne_zero_gammaTop.{u}
      apply germ_injective_of_isIntegral specInt.{u} (g x) (Set.mem_univ (g x))
      rw [map_ofNat, map_zero]
      exact h
    let := (g.stalkMap x).hom.toAlgebra
    have : Module.Flat (specInt.{u}.presheaf.stalk (g x)) (T.presheaf.stalk x) :=
      Flat.stalkMap g x
    have hr := IsSMulRegular.of_flat (S := T.presheaf.stalk x) (IsRegular.of_ne_zero h2).left
    rw [map_ofNat] at hr
    rw [map_zero]
    apply hr.right_eq_zero_of_smul
    have := congrArg (T.presheaf.germ ⊤ x hx) hz
    rw [smul_eq_mul, map_mul, map_ofNat, map_zero] at this
    exact this
  intro a b hab
  refine hreg ?_
  simp only [smul_eq_mul, two_mul]
  exact hab

/-- `1 + 1 = 0` in the global sections of `Spec(𝔽₂)`. -/
theorem one_add_one_gammaTop_specFTwo : (1 + 1 : (Γ(specFTwo.{u}, ⊤) : Type u)) = 0 := by
  change (1 + 1 : (Γ(Spec (.of (ULift.{u} (ZMod 2))), ⊤) : Type u)) = 0
  apply (Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod 2)))).commRingCatIsoToRingEquiv.injective
  rw [map_add, map_one, map_zero]
  decide

/-- The global sections of `Spec(𝔽₂)` are a nontrivial ring. -/
theorem nontrivial_gammaTop_specFTwo : Nontrivial (Γ(specFTwo.{u}, ⊤) : Type u) := by
  change Nontrivial (Γ(Spec (.of (ULift.{u} (ZMod 2))), ⊤) : Type u)
  exact (Scheme.ΓSpecIso
    (CommRingCat.of (ULift.{u} (ZMod 2)))).commRingCatIsoToRingEquiv.toEquiv.nontrivial

variable (B : BigFppfSite.{u})

local notation "hZ" => contains_specInt B

/-- `1 + 1 = 0` in the global sections of an object of the big site over `Spec(ℤ)` which maps to
`Spec(𝔽₂) → Spec(ℤ)`. -/
theorem one_add_one_gammaTop_of_hom {Z : BigFppfOver B specInt.{u} hZ} (g : Z ⟶ ftwoObject B) :
    (1 + 1 : (Γ((BigFppfOver.toScheme B specInt.{u} hZ).obj Z, ⊤) : Type u)) = 0 := by
  have h := congrArg ((BigFppfOver.toScheme B specInt.{u} hZ).map g).appTop.hom
    one_add_one_gammaTop_specFTwo.{u}
  rw [map_add, map_one, map_zero] at h
  exact h

/-- The global sections of an object of the big site over `Spec(ℤ)` equal to
`Spec(𝔽₂) → Spec(ℤ)` are a nontrivial ring. -/
theorem nontrivial_gammaTop_of_eq {Z : BigFppfOver B specInt.{u} hZ} (h : Z = ftwoObject B) :
    Nontrivial (Γ((BigFppfOver.toScheme B specInt.{u} hZ).obj Z, ⊤) : Type u) := by
  subst h
  exact nontrivial_gammaTop_specFTwo.{u}

/-! ### The data of the example -/

/-- `Spec(ℤ)` as the terminal object of the big site over `Spec(ℤ)`. -/
abbrev intObject : BigFppfOver B specInt.{u} hZ := Over.mk (𝟙 _)

/-- The closed immersion `Spec(𝔽₂) → Spec(ℤ)`, as a morphism of the big site over `Spec(ℤ)`. -/
def ftwoToInt : ftwoObject B ⟶ intObject B := Over.homMk (ftwoObject B).hom (Category.comp_id _)

/-- `𝒳`: the algebraic stack of the scheme `Spec(ℤ)`. -/
abbrev intStack : AlgebraicStacks.{u, w} B specInt.{u} hZ := schemeStack.{u, w} B _ _ (intObject B)

/-- `U = Spec(𝔽₂)`, as an algebraic space over `Spec(ℤ)`. -/
abbrev ftwoSpace : (BigFppfOver B specInt.{u} hZ)ᵒᵖ ⥤ Type u := yoneda.obj (ftwoObject B)

/-- `U = Spec(𝔽₂)` is an algebraic space. -/
theorem isAlgebraicSpace_ftwoSpace : IsAlgebraicSpace B specInt.{u} hZ (ftwoSpace B) :=
  isAlgebraicSpace_yoneda B _ _ (ftwoObject B)

/-- `f : 𝒰 ⟶ 𝒳`, the 1-morphism induced by `Spec(𝔽₂) → Spec(ℤ)`. -/
abbrev reductionMap :
    algebraicSpaceStack.{u, w} B specInt.{u} hZ (ftwoSpace B) (isAlgebraicSpace_ftwoSpace B) ⟶
      intStack.{u, w} B :=
  algebraicSpaceStackChart.{u, w} B _ _ (ftwoObject B) (schemeStackMap B _ _ (ftwoToInt B))

/-- `𝒪_𝒳`, as an object of `QCoh(𝒪_𝒳)`. -/
def structureQcoh : quasicoherentModules B specInt.{u} hZ (intStack.{u, w} B) :=
  ⟨SheafOfModules.unit _, SheafOfModules.isQuasicoherentOnSite_unit _⟩

/-- Multiplication by `2` on `𝒪_𝒳`, as a morphism of `QCoh(𝒪_𝒳)`. -/
def twoQcoh : structureQcoh.{u, w} B ⟶ structureQcoh.{u, w} B :=
  ObjectProperty.homMk (𝟙 _ + 𝟙 _)

/-- **Multiplication by `2` on `𝒪_𝒳` is a monomorphism of `QCoh(𝒪_𝒳)`**, for `𝒳` the stack of
`Spec(ℤ)`: over a flat object `T → Spec(ℤ)` it is multiplication by `2` on `Γ(T, 𝒪_T)`, which is
injective. -/
theorem mono_twoQcoh : Mono (twoQcoh.{u, w} B) := by
  refine mono_of_injective_app_flatObject _ fun y hy => ?_
  have hfl := (flatObject_schemeStack_iff.{u, w} B _ _ (intObject B) y).1 hy
  have : Flat ((BigFppfOver.toScheme B specInt.{u} hZ).map y.hom : _ ⟶ specInt.{u}) := hfl
  have hinj := injective_add_self_of_flat
    ((BigFppfOver.toScheme B specInt.{u} hZ).map y.hom : _ ⟶ specInt.{u})
  exact fun a b hab => hinj hab

/-! ### The image under `d` -/

/-- The functor `d` of the example. -/
abbrev d := qcohSpaceRestriction.{u, w} B specInt.{u} hZ (intStack.{u, w} B) (ftwoSpace B)
  (isAlgebraicSpace_ftwoSpace B) (reductionMap.{u, w} B)

/-- The functor `U_étale ⥤ 𝒳` along which `d` restricts. -/
abbrev chartFunctor :=
  Space.etaleChartToFibred (U := ⟨ftwoSpace B, isAlgebraicSpace_ftwoSpace B⟩) B specInt.{u} hZ
    (algebraicSpaceStack.{u, w} B _ _ (ftwoSpace B) (isAlgebraicSpace_ftwoSpace B)).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor (reductionMap.{u, w} B).hom)

/-- The object of the site underlying the image of an étale chart `W` of `U` in `𝒳` is the object
underlying `W`. -/
theorem p_obj_chartFunctor_obj (W : Space.SmallEtale B specInt.{u} hZ (ftwoSpace B)) :
    (intStack.{u, w} B).val.val.p.obj ((chartFunctor.{u, w} B).obj W) =
      (Space.SmallEtale.toOver B _ _ (ftwoSpace B)).obj W :=
  Functor.congr_obj
    (Space.etaleChartToFibred_comp (U := ⟨ftwoSpace B, isAlgebraicSpace_ftwoSpace B⟩)
    B specInt.{u} hZ
    (algebraicSpaceStack.{u, w} B _ _ (ftwoSpace B) (isAlgebraicSpace_ftwoSpace B)).val.val.p
    (intStack.{u, w} B).val.val.p
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor (reductionMap.{u, w} B).hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B _ _ (reductionMap.{u, w} B).hom)) W

/-- Over every étale chart of `U = Spec(𝔽₂)`, the sections of `d(𝒪_𝒳)` are killed by `2`. -/
theorem add_self_eq_zero (W : Space.SmallEtale B specInt.{u} hZ (ftwoSpace B))
    (s : (Γ((BigFppfOver.toScheme B specInt.{u} hZ).obj
      ((intStack.{u, w} B).val.val.p.obj ((chartFunctor.{u, w} B).obj W)), ⊤) : Type u)) :
    s + s = 0 := by
  have h := one_add_one_gammaTop_of_hom B
    (eqToHom (p_obj_chartFunctor_obj.{u, w} B W) ≫ yoneda.preimage W.obj.hom)
  rw [← one_mul s, ← add_mul, h, zero_mul]

/-- The identity chart of `U = Spec(𝔽₂)`. -/
def identityChart : Space.SmallEtale B specInt.{u} hZ (ftwoSpace B) :=
  ⟨CostructuredArrow.mk (𝟙 (ftwoSpace B)),
    presheaf_id_of_iso B _ _ _ (fun X Y f _ => by
      dsimp only [MorphismProperty.inverseImage]
      infer_instance) (ftwoObject B)⟩

/-- **The image of multiplication by `2` under `d` is not a monomorphism.** -/
theorem not_mono_map_twoQcoh : ¬ Mono ((d.{u, w} B).map (twoQcoh.{u, w} B)) := by
  intro hm
  have key : 𝟙 _ ≫ (d.{u, w} B).map (twoQcoh.{u, w} B) =
      (d.{u, w} B).map (twoQcoh.{u, w} B) ≫ (d.{u, w} B).map (twoQcoh.{u, w} B) := by
    refine ObjectProperty.hom_ext _ (SheafOfModules.hom_ext (PresheafOfModules.hom_ext ?_))
    intro W
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    exact (add_self_eq_zero.{u, w} B W.unop s).trans
      (add_self_eq_zero.{u, w} B W.unop (s + s)).symm
  have hid := (cancel_mono _).1 key
  obtain ⟨one, hone⟩ : ∃ x : (Γ((BigFppfOver.toScheme B specInt.{u} hZ).obj
      ((intStack.{u, w} B).val.val.p.obj ((chartFunctor.{u, w} B).obj (identityChart B))), ⊤) :
        Type u), x = 1 := ⟨_, rfl⟩
  have h1 := congrArg (fun k => (k.hom.val.app (op (identityChart B))).hom one) hid
  have h0 : one = 0 := h1.trans (add_self_eq_zero.{u, w} B (identityChart B) one)
  have hnt := nontrivial_gammaTop_of_eq B (p_obj_chartFunctor_obj.{u, w} B (identityChart B))
  exact one_ne_zero (hone ▸ h0)

end QcohSpaceRestrictionNonExact

/-- **Stacks 0GQS, item (4), non-exactness.**  On every big fppf site, for `𝒳` the algebraic stack
of `Spec(ℤ)` over `Spec(ℤ)` and `f` the 1-morphism from `U = Spec(𝔽₂)` induced by the closed
immersion `Spec(𝔽₂) → Spec(ℤ)`, the functor `d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` does not
preserve finite limits: it carries the monomorphism `2 : 𝒪_𝒳 → 𝒪_𝒳` to a morphism which is not a
monomorphism. -/
theorem not_preservesFiniteLimits_qcohSpaceRestriction_of_site (B : BigFppfSite.{u}) :
    ¬ PreservesFiniteLimits (qcohSpaceRestriction.{u, w} B AssociatedModuleNotExact.specInt.{u}
      (AssociatedModuleNotExact.contains_specInt B)
      (QcohSpaceRestrictionNonExact.intStack.{u, w} B) (QcohSpaceRestrictionNonExact.ftwoSpace B)
      (QcohSpaceRestrictionNonExact.isAlgebraicSpace_ftwoSpace B)
      (QcohSpaceRestrictionNonExact.reductionMap.{u, w} B)) := by
  intro h
  have := QcohSpaceRestrictionNonExact.mono_twoQcoh.{u, w} B
  exact QcohSpaceRestrictionNonExact.not_mono_map_twoQcoh.{u, w} B inferInstance

/-- **Stacks 0GQS, item (4): `d` is not exact in general.**  In every universe there are a big fppf
site `B`, a scheme `S` in it, an algebraic stack `𝒳` over `S`, an algebraic space `U` over `S` and a
1-morphism `f : 𝒰 ⟶ 𝒳` from the algebraic stack of `U` such that
`d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` does not preserve finite limits. -/
theorem not_preservesFiniteLimits_qcohSpaceRestriction :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (hU : IsAlgebraicSpace B S hS U) (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳),
      ¬ PreservesFiniteLimits (qcohSpaceRestriction B S hS 𝒳 U hU f) := by
  obtain ⟨B, -⟩ := BigFppfSite.exists_contains (AssociatedModuleNotExact.specInt.{u})
  exact ⟨B, _, _, _, _, _, _, not_preservesFiniteLimits_qcohSpaceRestriction_of_site.{u, w} B⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
