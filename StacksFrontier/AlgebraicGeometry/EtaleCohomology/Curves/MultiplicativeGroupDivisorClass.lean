module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointSkyscraperSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OrderOfVanishingSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreFunctionFieldIso

/-!
# `H¹(X, 𝐆_m)` of a smooth curve is its divisor class group

Let `X` be a smooth curve over an algebraically closed field `k`, with function field `K`. The
divisor sequence `0 → 𝐆_m → j_* 𝐆_{m,K} → ⨁_{x ∈ X_0} i_{x,*} 𝐙 → 0` (Stacks 03RI) and
`H¹(X, j_* 𝐆_{m,K}) = 0` (Stacks 03RK) give `H¹(X, 𝐆_m) = Γ(X, ⨁_x i_{x,*} 𝐙)/Γ(X, j_*𝐆_{m,K})`
(`Stacks.EtaleCohomology.divisorBoundary`). This file computes both global sections:

* the global sections of `⨁_x i_{x,*} 𝐙` are the finitely supported functions on the closed points,
  the sheaf coproduct having the direct sum of the sections of the summands as its sections over
  the quasi-compact quasi-separated `X`;
* the second map on global sections is `f ↦ ∑_x ord_x(f) [x]` on `K^*`.

So `H¹(X, 𝐆_m) ≅ (X_0 →₀ 𝐙)/div(K^*)`, the class group of Weil divisors supported on closed
points, the divisor `[x]` going to the connecting image of the section `1` of `i_{x,*} 𝐙`. This is
the curve case of Stacks 03P8 (`H¹_ét(X, 𝐆_m) = Pic(X)`) read through the Weil divisor class group.

## Main definitions

* `Stacks.EtaleCohomology.curveDivisorOfUnit`: `f ↦ ∑_x ord_x(f) [x]` on `K^*`.
* `Stacks.EtaleCohomology.curveClassGroup`: `(X_0 →₀ 𝐙)/div(K^*)`.
* `Stacks.EtaleCohomology.sheafHOneMultiplicativeEquivCurveClassGroup`:
  `H¹(X, 𝐆_m) ≃+ (X_0 →₀ 𝐙)/div(K^*)`.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI)
* [Stacks Project, Tag 03RK](https://stacks.math.columbia.edu/tag/03RK)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

namespace closedPointDivisorSheaf

variable (X : Scheme.{u})

/-- **Finitely supported families of sections of the summands give distinct sections of
`⨁_x i_{x,*} 𝐙`.** -/
theorem injective_sheafSectionOfDirectSum (U : X.Etale) :
    Function.Injective (sheafSectionOfDirectSum.{u, v} X U) :=
  (injective_iff_map_eq_zero _).2 fun f hf ↦ DFinsupp.ext fun x ↦
    eq_zero_of_sheafSectionOfDirectSum_eq_zero.{u, v} X U f hf x

/-- **Over a quasi-compact quasi-separated étale `X`-scheme every section of `⨁_x i_{x,*} 𝐙` is a
finite sum of sections of the summands** (`mem_closure_closedPointDivisorSheaf_sections`). -/
theorem surjective_sheafSectionOfDirectSum (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] :
    Function.Surjective (sheafSectionOfDirectSum.{u, v} X U) := by
  let _ : DecidableEq ↥(closedPoints X) := Classical.decEq _
  intro s
  refine (AddSubgroup.closure_le (sheafSectionOfDirectSum.{u, v} X U).range).2 ?_
    (mem_closure_closedPointDivisorSheaf_sections.{v, u} X U s)
  rintro _ ⟨-, ⟨x, rfl⟩, t, rfl⟩
  exact ⟨DirectSum.of _ x t, by rw [sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]⟩

/-- **The sections of `⨁_x i_{x,*} 𝐙` over a qcqs étale `X`-scheme are the direct sum of the
sections of the summands.** -/
def sectionsAddEquivDirectSum (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left] :
    DirectSum ↥(closedPoints X)
        (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U)) ≃+
      (closedPointDivisorSheaf.{u, v} X).obj.obj (op U) :=
  AddEquiv.ofBijective (sheafSectionOfDirectSum.{u, v} X U)
    ⟨injective_sheafSectionOfDirectSum.{u, v} X U, surjective_sheafSectionOfDirectSum.{u, v} X U⟩

/-- Reading a section built from a finitely supported family back as a family recovers it. -/
theorem sectionsAddEquivDirectSum_symm_apply (U : X.Etale) [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (f : DirectSum ↥(closedPoints X)
      fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj.obj (op U)) :
    (sectionsAddEquivDirectSum.{u, v} X U).symm (sheafSectionOfDirectSum.{u, v} X U f) = f :=
  (sectionsAddEquivDirectSum.{u, v} X U).symm_apply_apply f

end closedPointDivisorSheaf

/-! ### Global sections of the skyscrapers -/

section Top

variable (X : Scheme.{u})

/-- A locally constant map on a one-point space is its value at the point. -/
def locallyConstantAddEquivOfSubsingleton {T : Type*} [TopologicalSpace T] [Subsingleton T]
    (p : T) (A : Type*) [AddCommGroup A] : LocallyConstant T A ≃+ A where
  toFun f := f p
  invFun a := LocallyConstant.const T a
  left_inv f := LocallyConstant.ext fun y => congrArg f (Subsingleton.elim p y)
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The fibre of `X` itself over a point `x` is a single point**, the fibre of the identity. -/
theorem subsingleton_residueFibre_etaleMkId (x : X) :
    Subsingleton ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj
      (Scheme.Etale.mk (𝟙 X))).left :=
  subsingleton_pullback_fromSpecResidueField (𝟙 X) x fun a ha b hb => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
    rw [Scheme.Hom.id_base, TopCat.id_app] at ha hb
    exact ha.trans hb.symm

/-- The point of the fibre of `X` itself over a point `x`. -/
def residueFibreEtaleMkIdPoint (x : X) :
    ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj (Scheme.Etale.mk (𝟙 X))).left :=
  (nonempty_pullback_fromSpecResidueField (𝟙 X) (z := x) rfl).some

/-- **The global sections of `i_{x,*} 𝐙` are `𝐙`**: the fibre of `X` over `x` is one point. -/
def integerSkyscraperTopAddEquiv (x : X) :
    (integerSkyscraper.{u, v} X x).obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≃+ ℤ :=
  haveI := subsingleton_residueFibre_etaleMkId X x
  ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x
    (Scheme.Etale.mk (𝟙 X))).addCommGroupIsoToAddEquiv.trans
      (locallyConstantAddEquivOfSubsingleton (residueFibreEtaleMkIdPoint X x) _)).trans
    AddEquiv.ulift

end Top

/-! ### The second map on global sections -/

section SecondMap

variable (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
  [NoetherianSpace X]

/-- `X` itself, as an étale `X`-scheme, is locally Noetherian when `X` is. -/
instance isLocallyNoetherian_etaleMkId_left :
    IsLocallyNoetherian (Scheme.Etale.mk (𝟙 X)).left :=
  inferInstanceAs (IsLocallyNoetherian X)

/-- `X` itself, as an étale `X`-scheme, has a Noetherian space when `X` does. -/
instance noetherianSpace_etaleMkId_left : NoetherianSpace (Scheme.Etale.mk (𝟙 X)).left :=
  inferInstanceAs (NoetherianSpace X)

/-- **On global sections the second map of Stacks 03RI is the family of orders of vanishing**:
the morphism of sheaves `divisorSequenceSecondMap`, built on the affine étale site, agrees over
`X` itself with `closedPointDivisorSheafSection`, both being compatible with restriction to the
affine étale `X`-schemes, which cover `X`. -/
theorem divisorSequenceSecondMap_app_etaleMkId
    (z : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj
        (op (Scheme.Etale.mk (𝟙 X))))) :
    ((divisorSequenceSecondMap.{u, v} X).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom z =
      closedPointDivisorSheafSection.{u, v} (Scheme.Etale.mk (𝟙 X)) z.down := by
  refine Functor.IsCoverDense.ext (G := Scheme.AffineEtale.Spec X)
    ((sheafCompose _ (forget AddCommGrpCat.{max (u + 1) v})).obj
      (closedPointDivisorSheaf.{u, v} X)) _ fun W f => ?_
  have : IsLocallyNoetherian ((Scheme.AffineEtale.Spec X).obj W).left :=
    isLocallyNoetherian_etale_left X _
  have : NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
    noetherianSpace_affineEtale_left X W
  change ((closedPointDivisorSheaf.{u, v} X).obj.map f.op).hom _ =
    ((closedPointDivisorSheaf.{u, v} X).obj.map f.op).hom _
  rw [← ConcreteCategory.comp_apply, ← (divisorSequenceSecondMap.{u, v} X).hom.naturality,
    ConcreteCategory.comp_apply]
  refine (DFunLike.congr_fun (congrArg (fun φ => ConcreteCategory.hom φ)
    (divisorSequenceSecondMap_hom_app.{u, v} X W)) _).trans ?_
  refine (affineEtaleDivisorApp_apply.{u, v} X W _).trans ?_
  refine (congrArg (closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj W))
    (genericPointDirectImage_multiplicativeSheaf_map_down.{u, v} X f z)).trans ?_
  exact (closedPointDivisorSheafSection_map.{u, v} f (Additive.toMul z.down)).symm

end SecondMap

/-! ### Divisors supported on closed points -/

section ClassGroup

variable (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X]
  [NoetherianSpace X]

/-- **The divisor of an invertible rational function, supported on the closed points**:
`f ↦ ∑_x ord_x(f) [x]`, finitely supported because a rational function has finitely many zeros
and poles. -/
def closedPointDivisorOfUnit : Additive (X.functionField)ˣ →+ (closedPoints X →₀ ℤ) where
  toFun f := Finsupp.ofSupportFinite (fun x : closedPoints X => Scheme.ordAddMonoidHom x.1 f)
    ((Scheme.finite_support_ord
      ((Additive.toMul f : (X.functionField)ˣ) : X.functionField)).preimage
        Subtype.val_injective.injOn)
  map_zero' := Finsupp.ext fun x => map_zero (Scheme.ordAddMonoidHom x.1)
  map_add' f f' := Finsupp.ext fun x => map_add (Scheme.ordAddMonoidHom x.1) f f'

/-- The coefficient of `div(f)` at `x` is `ord_x(f)`. -/
@[simp]
theorem closedPointDivisorOfUnit_apply (f : Additive (X.functionField)ˣ) (x : closedPoints X) :
    closedPointDivisorOfUnit X f x =
      Scheme.ord ((Additive.toMul f : (X.functionField)ˣ) : X.functionField) x.1 :=
  rfl

/-- **The class group of divisors supported on the closed points**, `(X_0 →₀ 𝐙)/div(K^*)`. On a
curve every prime divisor is a closed point, so this is the Weil divisor class group. -/
abbrev closedPointClassGroup : Type u :=
  (closedPoints X →₀ ℤ) ⧸ (closedPointDivisorOfUnit X).range

end ClassGroup

/-! ### Global divisors -/

section Divisors

variable (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] [IsNormal X] [IsLocallyNoetherian X]
  [NoetherianSpace X] [QuasiSeparatedSpace X]

/-- `X` itself, as an étale `X`-scheme, is quasi-compact when `X` is. -/
instance compactSpace_etaleMkId_left : CompactSpace (Scheme.Etale.mk (𝟙 X)).left :=
  inferInstanceAs (CompactSpace X)

/-- `X` itself, as an étale `X`-scheme, is quasi-separated when `X` is. -/
instance quasiSeparatedSpace_etaleMkId_left :
    QuasiSeparatedSpace (Scheme.Etale.mk (𝟙 X)).left :=
  inferInstanceAs (QuasiSeparatedSpace X)

/-- **The global sections of `⨁_x i_{x,*} 𝐙` are the finitely supported `𝐙`-valued functions on
the closed points.** -/
def closedPointDivisorSheafTopAddEquiv :
    (closedPointDivisorSheaf.{u, v} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≃+
      (closedPoints X →₀ ℤ) :=
  letI : DecidableEq ↥(closedPoints X) := Classical.decEq _
  ((closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X
    (Scheme.Etale.mk (𝟙 X))).symm.trans
      (DFinsupp.mapRange.addEquiv fun x : closedPoints X =>
        integerSkyscraperTopAddEquiv.{u, v} X x.1)).trans
    (finsuppAddEquivDFinsupp (M := ℤ)).symm

omit [AlgebraicGeometry.IsIntegral X] [IsNormal X] [IsLocallyNoetherian X] in
/-- The coefficient at `x` of a global divisor is the integer of its `x`-component. -/
theorem closedPointDivisorSheafTopAddEquiv_apply
    (s : (closedPointDivisorSheaf.{u, v} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))
    (x : closedPoints X) :
    closedPointDivisorSheafTopAddEquiv.{u, v} X s x = integerSkyscraperTopAddEquiv.{u, v} X x.1
      ((closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X
        (Scheme.Etale.mk (𝟙 X))).symm s x) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  rw [closedPointDivisorSheafTopAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    finsuppAddEquivDFinsupp_symm_apply, DFinsupp.toFinsupp_coe]
  rfl

omit [NoetherianSpace X] [QuasiSeparatedSpace X] in
/-- **The integer attached to an invertible rational function at a point is its order of
vanishing there.** -/
theorem integerSkyscraperTopAddEquiv_integerSkyscraperDivisorOfPoint (x : X)
    (a : Additive ((Γ(pullback (Scheme.Etale.mk (𝟙 X)).hom (genericPointInclusion X), ⊤))ˣ)) :
    integerSkyscraperTopAddEquiv.{u, v} X x
        (integerSkyscraperDivisorOfPoint.{u, v} (Scheme.Etale.mk (𝟙 X)) x a) =
      haveI : AlgebraicGeometry.IsIntegral (Scheme.Etale.mk (𝟙 X)).left :=
        inferInstanceAs (AlgebraicGeometry.IsIntegral X)
      etaleGenericFibreOrd (Scheme.Etale.mk (𝟙 X)) x a := by
  have hp : (pullback.fst (Scheme.Etale.mk (𝟙 X)).hom (X.fromSpecResidueField x))
      (residueFibreEtaleMkIdPoint X x) = x :=
    hom_base_pullback_fst_fromSpecResidueField x (Scheme.Etale.mk (𝟙 X)) _
  change ULift.down (((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x
      (Scheme.Etale.mk (𝟙 X))).hom.hom ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v}
        X x (Scheme.Etale.mk (𝟙 X))).inv.hom (residueFibreOrdOfPoint.{u, v} _ x a)))
          (residueFibreEtaleMkIdPoint X x)) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply,
    residueFibreOrdOfPoint_apply, hp]
  have : AlgebraicGeometry.IsIntegral (Scheme.Etale.mk (𝟙 X)).left :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral X)
  exact (etaleGenericFibreOrdOfPoint_eq_etaleGenericFibreOrd (X := X)
    (Scheme.Etale.mk (𝟙 X)) x a :)

omit [IsLocallyNoetherian X] [NoetherianSpace X] [QuasiSeparatedSpace X] in
/-- The section of `⨁_x i_{x,*} 𝐙` attached to a unit on the generic fibre, read as a
finitely supported family, is its family of orders of vanishing. -/
theorem sectionsAddEquivDirectSum_symm_closedPointDivisorSheafSection (U : X.Etale)
    [IsLocallyNoetherian U.left] [NoetherianSpace U.left] [CompactSpace U.left]
    [QuasiSeparatedSpace U.left]
    (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ)) :
    (closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).symm
        (closedPointDivisorSheafSection.{u, v} U a) = closedPointDivisorSections.{u, v} U a :=
  (congrArg (closedPointDivisorSheaf.sectionsAddEquivDirectSum.{u, v} X U).symm
    (closedPointDivisorSheafSection_apply.{u, v} U a)).trans
      (closedPointDivisorSheaf.sectionsAddEquivDirectSum_symm_apply.{u, v} X U _)

/-- **The second map on global sections is the divisor of a rational function**: read through
`closedPointDivisorSheafTopAddEquiv`, the image of a section of `j_* 𝐆_{m,K}` over `X` is the
divisor of the corresponding rational function. -/
theorem closedPointDivisorSheafTopAddEquiv_divisorSequenceSecondMap
    (z : ULift.{max (u + 1) v} (Additive
      ((Γ(pullback (Scheme.Etale.mk (𝟙 X)).hom (genericPointInclusion X), ⊤))ˣ))) :
    closedPointDivisorSheafTopAddEquiv.{u, v} X
        (((divisorSequenceSecondMap.{u, v} X).hom.app (op (Scheme.Etale.mk (𝟙 X)))).hom z) =
      closedPointDivisorOfUnit X (Additive.ofMul (Units.map
        (genericFibreToFunctionField (X := X) (U := X) (𝟙 X)).hom.toMonoidHom
          (Additive.toMul z.down))) := by
  refine Finsupp.ext fun x => ?_
  rw [closedPointDivisorSheafTopAddEquiv_apply, divisorSequenceSecondMap_app_etaleMkId.{u, v} X z,
    sectionsAddEquivDirectSum_symm_closedPointDivisorSheafSection]
  obtain ⟨a⟩ := z
  dsimp only
  exact (congrArg (integerSkyscraperTopAddEquiv.{u, v} X x.1)
    (closedPointDivisorSections_apply.{u, v} (Scheme.Etale.mk (𝟙 X)) a x)).trans
      ((integerSkyscraperTopAddEquiv_integerSkyscraperDivisorOfPoint.{u, v} X x.1 a).trans
        (genericFibreOrd_apply (X := X) (U := X) (𝟙 X) x.1 a))

end Divisors

/-! ### `H¹(X, 𝐆_m)` as the divisor class group -/

section Curve

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g]

omit [IsAlgClosed k] in
include g in
/-- The hypotheses on `X` under which the divisors of a smooth curve are computed above. -/
theorem isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve :
    IsNormal X ∧ IsLocallyNoetherian X ∧ NoetherianSpace X ∧ QuasiSeparatedSpace X := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  exact ⟨isNormal_of_isCurve_of_smooth g, inferInstance, inferInstance,
    quasiSeparatedSpace_of_quasiSeparated g⟩

omit [IsAlgClosed k] in
/-- **The kernel of the connecting map is the group of principal divisors.** -/
theorem map_ker_divisorBoundary
    [IsNormal X] [IsLocallyNoetherian X] [NoetherianSpace X] [QuasiSeparatedSpace X] :
    (divisorBoundary g).ker.map (closedPointDivisorSheafTopAddEquiv.{u, u + 1} X).toAddMonoidHom =
      (closedPointDivisorOfUnit X).range := by
  ext d
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨z, rfl⟩ := (divisorBoundary_eq_zero_iff g s).1 hs
    exact ⟨_, (closedPointDivisorSheafTopAddEquiv_divisorSequenceSecondMap.{u, u + 1} X z).symm⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨b, hb⟩ := surjective_units_map_genericFibreToFunctionField (X := X) (U := X) (𝟙 X)
      (Additive.toMul f)
    exact ⟨((divisorSequenceSecondMap.{u, u + 1} X).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))).hom (ULift.up (Additive.ofMul b)),
      (divisorBoundary_eq_zero_iff g _).2 ⟨_, rfl⟩,
      (closedPointDivisorSheafTopAddEquiv_divisorSequenceSecondMap.{u, u + 1} X
        (ULift.up (Additive.ofMul b))).trans
          (congrArg (closedPointDivisorOfUnit X) (congrArg Additive.ofMul hb))⟩

/-- **The divisor class group of a smooth curve**, `(X_0 →₀ 𝐙)/div(K^*)`: on a curve the closed
points are the prime divisors, so this is the Weil divisor class group. -/
abbrev curveClassGroup : Type u :=
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).2.1
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).2.2.1
  closedPointClassGroup X

/-- **`H¹(X, 𝐆_m)` of a smooth curve over an algebraically closed field is its divisor class
group** `(X_0 →₀ 𝐙)/div(K^*)` (Stacks 03P8 for curves, read through Weil divisors): the
connecting map of the divisor sequence identifies the quotient of the global divisors by the
principal ones with `H¹(X, 𝐆_m)`. -/
def sheafHOneMultiplicativeAddEquivClosedPointClassGroup :
    Sheaf.H.{u + 1} (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) 1 ≃+ curveClassGroup g :=
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).1
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).2.1
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).2.2.1
  haveI := (isNormal_isLocallyNoetherian_noetherianSpace_quasiSeparatedSpace_of_isCurve g).2.2.2
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_divisorBoundary g)).symm.trans
    (QuotientAddGroup.congr _ _ (closedPointDivisorSheafTopAddEquiv.{u, u + 1} X)
      (map_ker_divisorBoundary g))

/-- **The class of a divisor is its connecting image**: the identification sends the connecting
image of a global divisor to the class of the corresponding finitely supported function. -/
theorem sheafHOneMultiplicativeAddEquivClosedPointClassGroup_divisorBoundary
    [IsNormal X] [IsLocallyNoetherian X] [NoetherianSpace X] [QuasiSeparatedSpace X]
    (s : ToType ((closedPointDivisorSheaf.{u, u + 1} X).obj.obj (op (Scheme.Etale.mk (𝟙 X))))) :
    sheafHOneMultiplicativeAddEquivClosedPointClassGroup g (divisorBoundary g s) =
      (QuotientAddGroup.mk (closedPointDivisorSheafTopAddEquiv.{u, u + 1} X s) :
        closedPointClassGroup X) := by
  rw [sheafHOneMultiplicativeAddEquivClosedPointClassGroup, AddEquiv.trans_apply]
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_divisorBoundary g)).symm
      (divisorBoundary g s) = QuotientAddGroup.mk s :=
    (AddEquiv.symm_apply_eq _).2 rfl
  rw [h]
  rfl

end Curve

end Stacks.EtaleCohomology

end
