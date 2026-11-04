module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionAffineCharts
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension
public import StacksFrontier.AlgebraicGeometry.Thickenings.Transitivity

/-!
# The chart thickenings of a square-zero extension of the étale structure sheaf

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` on its small étale site, with `ℐ` quasi-coherent
(`AlgebraicGeometry.Space.SquareZeroExtension`, the data of Stacks 05ZT). For every étale chart
`U` of `X`, the restriction

```
0 ⟶ ℐ|_{U_Zar} ⟶ 𝒜|_{U_Zar} ⟶ 𝒪_U ⟶ 0
```

to the Zariski opens of `U` is a square-zero extension of schemes with quasi-coherent kernel
(Descent, Proposition 35.9.4), so More on Morphisms, Lemma 37.2.2 (Stacks 05YV) gives a
first-order thickening `U ⊂ U'` with `𝒪_{U'} ≅ 𝒜|_{U_Zar}`.

## Main definitions

* `AlgebraicGeometry.Scheme.thickenedLocallyRingedSpace`: the space of a scheme `X` carrying a
  sheaf of rings `𝒜` with a locally surjective `𝒜 ⟶ 𝒪_X` killing only sections of square zero,
  as a locally ringed space.
* `AlgebraicGeometry.Scheme.squareZeroExtensionOverSpecZ`: such data with a quasi-coherent
  square-zero kernel, as a `Stacks.Thickenings.SquareZeroExtension` over `Spec ℤ`; the structure
  morphism to `Spec ℤ` is the one every locally ringed space has.
* `AlgebraicGeometry.Scheme.realizedScheme`: the scheme realizing a square-zero extension of
  schemes whose structure sheaf is `𝒜` *on the nose*, and `realizedInclusion`, its first-order
  thickening `X ⟶ X'` (`isFirstOrderThickening_realizedInclusion`).
* `AlgebraicGeometry.Space.SquareZeroExtension.chartSheaf`, `chartπ`, `chartKernel`, `chartι`:
  the restriction of `𝒜`, of `𝒜 ⟶ 𝒪_X` and of the kernel to the Zariski opens of an étale chart.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartExtension`: the restricted extension, as a
  square-zero extension of the scheme of the chart over `Spec ℤ`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isLocallySurjective_chartπ`: `𝒜|_{U_Zar} ⟶ 𝒪_U`
  is locally surjective.
* `AlgebraicGeometry.Space.SquareZeroExtension.isFirstOrderThickening_chartInclusion`: the
  inclusion `U ⟶ U'` of an étale chart into its chart thickening is a first-order thickening.
* `IsLocalRing.of_surjective_of_isNilpotent_of_map_eq_zero`: a ring surjecting onto a local ring
  with nil kernel is local.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u


/-- A ring surjecting onto a local ring with a nil kernel is local. -/
theorem _root_.IsLocalRing.of_surjective_of_isNilpotent_of_map_eq_zero {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) (hφ : Function.Surjective φ)
    (hker : ∀ r, φ r = 0 → IsNilpotent r) : IsLocalRing R := by
  have hunit : ∀ a : R, IsUnit (φ a) → IsUnit a := by
    intro a ha
    obtain ⟨b, hb⟩ := hφ ↑(ha.unit⁻¹)
    have h1 : φ (a * b - 1) = 0 := by
      rw [map_sub, map_mul, hb, map_one]
      exact sub_eq_zero.2 ha.mul_val_inv
    have h2 := (hker _ h1).isUnit_add_left_of_commute isUnit_one (Commute.one_right _)
    rw [add_sub_cancel] at h2
    exact isUnit_of_mul_isUnit_left h2
  have : Nontrivial R := φ.domain_nontrivial
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (φ a)).imp (hunit a)
      (fun h => hunit _ (by rwa [map_sub, map_one]))


namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (A : TopCat.Sheaf CommRingCat.{u} X) (π : A ⟶ X.sheaf)

/-- The stalk map of a map of sheaves of rings `π : 𝒜 ⟶ 𝒪_X`. -/
abbrev sheafStalkMap (x : X) :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map π.hom

/-- If `π : 𝒜 ⟶ 𝒪_X` kills only sections of square zero, so does every stalk map. -/
theorem sheafStalkMap_mul_self_eq_zero
    (hsq : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V), π.hom.app V a = 0 → a * a = 0)
    (x : X) (g : A.presheaf.stalk x) (hg : sheafStalkMap A π x g = 0) : g * g = 0 := by
  obtain ⟨V, hxV, a, rfl⟩ := TopCat.Presheaf.germ_exist A.presheaf g
  rw [sheafStalkMap, TopCat.Presheaf.stalkFunctor_map_germ_apply] at hg
  have hg' : X.presheaf.germ V x hxV (π.hom.app (op V) a) = X.presheaf.germ V x hxV 0 :=
    hg.trans (map_zero _).symm
  obtain ⟨W, hxW, iU, iV, h⟩ := TopCat.Presheaf.germ_eq X.presheaf x hxV hxV _ _ hg'
  rw [map_zero] at h
  have h' : π.hom.app (op W) (A.presheaf.map iU.op a) = 0 :=
    (congrArg (fun q => q.hom a) (π.hom.naturality iU.op)).trans h
  rw [← TopCat.Presheaf.germ_res_apply A.presheaf iU x hxW a, ← map_mul,
    hsq _ _ h', map_zero]

/-- If `π : 𝒜 ⟶ 𝒪_X` is locally surjective and kills only sections of square zero, the stalks
of `𝒜` are local rings. -/
theorem isLocalRing_stalk_of_squareZero (hπ : TopCat.Presheaf.IsLocallySurjective π.hom)
    (hsq : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V), π.hom.app V a = 0 → a * a = 0)
    (x : X) : IsLocalRing (A.presheaf.stalk x) := by
  have hs := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks π.hom).1 hπ x
  let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) :=
    X.toLocallyRingedSpace.isLocalRing x
  exact IsLocalRing.of_surjective_of_isNilpotent_of_map_eq_zero (sheafStalkMap A π x).hom hs
    fun g hg => ⟨2, by rw [pow_two]; exact sheafStalkMap_mul_self_eq_zero A π hsq x g hg⟩

/-- The space of `X` carrying a sheaf of rings `𝒜` with a locally surjective map `𝒜 ⟶ 𝒪_X`
killing only sections of square zero, as a locally ringed space. -/
def thickenedLocallyRingedSpace (hπ : TopCat.Presheaf.IsLocallySurjective π.hom)
    (hsq : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V), π.hom.app V a = 0 → a * a = 0) :
    LocallyRingedSpace.{u} where
  toSheafedSpace := Stacks.Thickenings.thickenedSpace X A
  isLocalRing := isLocalRing_stalk_of_squareZero A π hπ hsq

variable (hπ : TopCat.Presheaf.IsLocallySurjective π.hom)
  (hsq : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V), π.hom.app V a = 0 → a * a = 0)

/-- The canonical inclusion `X ⟶ (X, 𝒜)` of sheafed spaces, given by `π` on sections. -/
def thickenedInclusion : X.toSheafedSpace ⟶ Stacks.Thickenings.thickenedSpace X A :=
  InducedCategory.homMk { base := 𝟙 (X : TopCat), c := π.hom }

/-- The stalk maps of `AlgebraicGeometry.Scheme.thickenedInclusion` are those of `π`. -/
theorem thickenedInclusion_stalkMap (x : X) :
    (thickenedInclusion A π).hom.stalkMap x = sheafStalkMap A π x := by
  show (TopCat.Presheaf.stalkFunctor CommRingCat x).map π.hom ≫
      TopCat.Presheaf.stalkPushforward CommRingCat (𝟙 (X : TopCat)) X.presheaf x =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map π.hom
  rw [TopCat.Presheaf.stalkPushforward.id]
  show (TopCat.Presheaf.stalkFunctor CommRingCat x).map π.hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (TopCat.Presheaf.Pushforward.id X.presheaf).hom =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map π.hom
  refine Eq.trans ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp
    π.hom (TopCat.Presheaf.Pushforward.id X.presheaf).hom).symm ?_
  congr 1

include hπ hsq in
/-- The stalk maps of `AlgebraicGeometry.Scheme.thickenedInclusion` are local. -/
theorem thickenedInclusion_isLocalHom (x : X) :
    IsLocalHom ((thickenedInclusion A π).hom.stalkMap x).hom := by
  rw [thickenedInclusion_stalkMap]
  let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj A.obj) :=
    isLocalRing_stalk_of_squareZero A π hπ hsq x
  let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.sheaf.obj) :=
    X.toLocallyRingedSpace.isLocalRing x
  exact IsLocalHom.of_surjective (sheafStalkMap A π x).hom
    ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks π.hom).1 hπ x)

/-- The canonical inclusion `X ⟶ (X, 𝒜)` as a morphism of locally ringed spaces: its stalk maps
are surjections of local rings. -/
def thickenedInclusionLRS : X.toLocallyRingedSpace ⟶ thickenedLocallyRingedSpace A π hπ hsq :=
  LocallyRingedSpace.homMk (thickenedInclusion A π) fun x =>
    thickenedInclusion_isLocalHom A π hπ hsq x

/-- The structure morphism `(X, 𝒜) ⟶ Spec ℤ` of locally ringed spaces. -/
def thickenedToSpecZLRS :
    thickenedLocallyRingedSpace A π hπ hsq ⟶
      (Spec (CommRingCat.of (ULift.{u} ℤ))).toLocallyRingedSpace :=
  (thickenedLocallyRingedSpace A π hπ hsq).toΓSpec ≫
    Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom))

/-- The square-zero extension of `𝒪_X` by `𝒜`, over `Spec ℤ`: the data of Stacks 05YV for a
locally surjective `π : 𝒜 ⟶ 𝒪_X` with a prescribed quasi-coherent square-zero kernel. -/
def squareZeroExtensionOverSpecZ (I : X.Modules) (hI : I.IsQuasicoherent)
    (ι : ∀ V : (Opens X)ᵒᵖ, I.val.obj V →+ A.presheaf.obj V)
    (naturality : ∀ {V W : (Opens X)ᵒᵖ} (g : V ⟶ W) (x : I.val.obj V),
      ι W (I.val.map g x) = A.presheaf.map g (ι V x))
    (mem_kernel : ∀ (V : (Opens X)ᵒᵖ) (x : I.val.obj V), π.hom.app V (ι V x) = 0)
    (exact_kernel : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V),
      π.hom.app V a = 0 → ∃! x, ι V x = a)
    (smul_lift : ∀ (V : (Opens X)ᵒᵖ) (a : A.presheaf.obj V) (x : I.val.obj V),
      ι V (((I.val.obj V).smul (π.hom.app V a)).hom x) = a * ι V x)
    (square_zero : ∀ (V : (Opens X)ᵒᵖ) (x y : I.val.obj V), ι V x * ι V y = 0) :
    Stacks.Thickenings.SquareZeroExtension (specULiftZIsTerminal.from X) where
  A := A
  π := π
  locallySurjective_π := hπ
  inclusion := thickenedInclusion A π
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := (thickenedToSpecZLRS A π hπ hsq).toShHom
  over_base := by
    have h := specULiftZIsTerminal.hom_ext
      (Scheme.Hom.mk (thickenedInclusionLRS A π hπ hsq ≫ thickenedToSpecZLRS A π hπ hsq))
      (specULiftZIsTerminal.from X)
    exact congrArg (fun g : X ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) => g.toLRSHom.toShHom) h
  I := I
  quasicoherent := hI
  ι := ι
  naturality := naturality
  mem_kernel := mem_kernel
  exact_kernel := exact_kernel
  smul_lift := smul_lift
  square_zero := square_zero

section Realized

variable {T : Scheme.{u}} {g : X ⟶ T} (E' : Stacks.Thickenings.SquareZeroExtension g)

/-- In a square-zero extension of schemes, a section killed by the surjection squares to zero. -/
theorem squareZeroExtension_mul_self_eq_zero (V : (Opens X)ᵒᵖ) (a : E'.A.presheaf.obj V)
    (ha : E'.π.hom.app V a = 0) : a * a = 0 := by
  obtain ⟨x, rfl, -⟩ := E'.exact_kernel V a ha
  exact E'.square_zero V x x

/-- The space of `X` with the sheaf of rings `𝒜` of a square-zero extension, as a locally
ringed space. -/
abbrev realizedLRS : LocallyRingedSpace.{u} :=
  thickenedLocallyRingedSpace E'.A E'.π E'.locallySurjective_π
    (squareZeroExtension_mul_self_eq_zero E')

/-- The realization of Stacks 05YV is isomorphic, as a locally ringed space, to the space of `X`
carrying `𝒜`. -/
def realizedIso (r : Stacks.Thickenings.Realization E') :
    r.ambient.toLocallyRingedSpace ≅ realizedLRS E' :=
  LocallyRingedSpace.isoOfSheafedSpaceIso r.sheafedIso

/-- **The thickening realizing a square-zero extension, on the nose.** The underlying space of
`X` with structure sheaf *equal* to `𝒜`, as a scheme. -/
def realizedScheme : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (realizedLRS E') (by
    intro x
    let r := (Stacks.Thickenings.squareZeroExtension_realization E').some
    obtain ⟨R, h, hh, y, hy⟩ := Scheme.exists_Spec_apply_eq ((realizedIso E' r).inv.base x)
    refine ⟨R, h.toLRSHom ≫ (realizedIso E' r).hom, ⟨y, ?_⟩, ?_⟩
    · change (realizedIso E' r).hom.base (h.base y) = x
      rw [hy]
      exact ConcreteCategory.congr_hom
        (congrArg (fun q => q.base) (realizedIso E' r).inv_hom_id) x
    · exact LocallyRingedSpace.IsOpenImmersion.comp h.toLRSHom (realizedIso E' r).hom)

/-- The locally ringed space of `AlgebraicGeometry.Scheme.realizedScheme` is
`AlgebraicGeometry.Scheme.realizedLRS`. -/
theorem realizedScheme_toLocallyRingedSpace :
    (realizedScheme E').toLocallyRingedSpace = realizedLRS E' :=
  rfl

/-- The inclusion `X ⟶ X'` of a scheme into the scheme realizing a square-zero extension of its
structure sheaf: the identity on spaces, `π` on sections. -/
def realizedInclusion : X ⟶ realizedScheme E' :=
  Scheme.Hom.mk (thickenedInclusionLRS E'.A E'.π E'.locallySurjective_π
    (squareZeroExtension_mul_self_eq_zero E'))

/-- The canonical inclusion `X ⟶ (X, 𝒜)` is the inclusion of the square-zero extension. -/
theorem thickenedInclusion_eq_inclusion : thickenedInclusion E'.A E'.π = E'.inclusion := by
  apply InducedCategory.hom_ext
  apply PresheafedSpace.hext
  · exact E'.inclusion_base.symm
  · exact E'.inclusion_sheaf.symm

/-- The identification of the scheme of a realization of Stacks 05YV with `realizedScheme`. -/
def realizedSchemeIso (r : Stacks.Thickenings.Realization E') : r.ambient ≅ realizedScheme E' :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso (realizedIso E' r)

/-- The inclusion `X ⟶ X'` followed by the identification with the scheme of a realization is the
immersion of the realization. -/
theorem realizedInclusion_comp_realizedSchemeIso_inv (r : Stacks.Thickenings.Realization E') :
    realizedInclusion E' ≫ (realizedSchemeIso E' r).inv = r.immersion := by
  apply Scheme.forgetToLocallyRingedSpace.map_injective
  apply LocallyRingedSpace.Hom.ext'
  have h : thickenedInclusion E'.A E'.π ≫ r.sheafedIso.inv = r.immersion.toLRSHom.toShHom := by
    rw [thickenedInclusion_eq_inclusion, ← r.inclusion_eq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact congrArg (fun q => q.hom) h

/-- **`X ⟶ X'` is a first-order thickening** (Stacks 05YV, transported to the scheme whose
structure sheaf is `𝒜` on the nose). -/
theorem isFirstOrderThickening_realizedInclusion :
    Stacks.Thickenings.IsFirstOrderThickening (realizedInclusion E') := by
  let r := (Stacks.Thickenings.squareZeroExtension_realization E').some
  apply Stacks.Thickenings.IsFirstOrderThickening.of_comp_mono _ (realizedSchemeIso E' r).inv
  rw [realizedInclusion_comp_realizedSchemeIso_inv]
  exact r.immersion_isFirstOrder

end Realized

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable (U : SmallEtale B S hS X.1)

/-- The restriction `𝒜|_{U_Zar}` of the extension sheaf to the Zariski opens of an étale
chart `U`. -/
def chartSheaf : TopCat.Sheaf CommRingCat.{u} (chartScheme U) :=
  letI := isContinuous_chartOpens B S hS X.1 X.2 U
  ((chartOpens B S hS U).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology (chartScheme U)) (SmallEtale.topology B S hS X.1)).obj E.A

/-- The sections of `𝒜|_{U_Zar}` over an open `V` are the sections of `𝒜` over the chart `V`
cuts out. -/
theorem chartSheaf_obj (V : (chartScheme U).Opens) :
    (E.chartSheaf U).presheaf.obj (op V) = E.A.val.obj (op ((chartOpens B S hS U).obj V)) :=
  rfl

/-- The surjection `𝒜|_{U_Zar} ⟶ 𝒪_U`. -/
def chartπ : E.chartSheaf U ⟶ (chartScheme U).sheaf :=
  ⟨(Functor.whiskerLeft (chartOpens B S hS U).op E.π.hom : _ ⟶
      (chartScheme U).restrictFunctor.op ⋙ (Over.forget (chartScheme U)).op ⋙ Scheme.Γ) ≫
    (Scheme.restrictFunctorΓ (X := chartScheme U)).hom⟩

/-- The value of `𝒜|_{U_Zar} ⟶ 𝒪_U` on sections over an open `V` is that of `𝒜 ⟶ 𝒪_X` over the
chart `V` cuts out, followed by the comparison `Γ(V, ⊤) ≅ Γ(U, V)`. -/
theorem chartπ_app (V : (chartScheme U).Opens) (a : (E.chartSheaf U).presheaf.obj (op V)) :
    (E.chartπ U).hom.app (op V) a =
      (Scheme.restrictFunctorΓ (X := chartScheme U)).hom.app (op V)
        (E.π.hom.app (op ((chartOpens B S hS U).obj V)) a) :=
  rfl

/-- The kernel `ℐ|_{U_Zar}`. -/
abbrev chartKernel : (chartScheme U).Modules :=
  chartRestrictionSheaf B S hS X E.I U

/-- The inclusion of the kernel over the chart. -/
def chartι (V : (Opens (chartScheme U))ᵒᵖ) :
    (E.chartKernel U).val.obj V →+ (E.chartSheaf U).presheaf.obj V :=
  (E.ι ((chartOpens B S hS U).op.obj V)).comp AddEquiv.ulift.toAddMonoidHom

/-- The value of the inclusion of the kernel over the chart. -/
theorem chartι_apply (V : (Opens (chartScheme U))ᵒᵖ) (x : (E.chartKernel U).val.obj V) :
    E.chartι U V x = E.ι ((chartOpens B S hS U).op.obj V) x.down :=
  rfl

/-- The inclusion of the kernel over the chart commutes with restriction. -/
theorem chartι_naturality {V W : (Opens (chartScheme U))ᵒᵖ} (g : V ⟶ W)
    (x : (E.chartKernel U).val.obj V) :
    E.chartι U W ((E.chartKernel U).val.map g x) =
      (E.chartSheaf U).presheaf.map g (E.chartι U V x) :=
  E.naturality ((chartOpens B S hS U).op.map g) x.down

/-- The comparison `Γ(V, ⊤) ≅ Γ(U, V)` at an open of the chart, as a ring isomorphism. -/
abbrev chartΓEquiv (V : (Opens (chartScheme U))ᵒᵖ) :=
  ((Scheme.restrictFunctorΓ (X := chartScheme U)).app V).commRingCatIsoToRingEquiv

/-- The value of `𝒜|_{U_Zar} ⟶ 𝒪_U` on sections, through the ring isomorphism
`AlgebraicGeometry.Space.SquareZeroExtension.chartΓEquiv`. -/
theorem chartπ_apply' (V : (Opens (chartScheme U))ᵒᵖ) (a : (E.chartSheaf U).presheaf.obj V) :
    (E.chartπ U).hom.app V a = chartΓEquiv U V (E.π.hom.app ((chartOpens B S hS U).op.obj V) a) :=
  rfl

/-- The kernel over the chart is killed by `𝒜|_{U_Zar} ⟶ 𝒪_U`. -/
theorem chartπ_chartι (V : (Opens (chartScheme U))ᵒᵖ) (x : (E.chartKernel U).val.obj V) :
    (E.chartπ U).hom.app V (E.chartι U V x) = 0 :=
  (congrArg (chartΓEquiv U V) (E.mem_kernel _ x.down)).trans (map_zero _)

/-- A section of `𝒜|_{U_Zar}` is killed by `𝒜|_{U_Zar} ⟶ 𝒪_U` if and only if it is killed by
`𝒜 ⟶ 𝒪_X`. -/
theorem chartπ_eq_zero_iff (V : (Opens (chartScheme U))ᵒᵖ)
    (a : (E.chartSheaf U).presheaf.obj V) :
    (E.chartπ U).hom.app V a = 0 ↔ E.π.hom.app ((chartOpens B S hS U).op.obj V) a = 0 := by
  rw [chartπ_apply']
  exact map_eq_zero_iff _ (chartΓEquiv U V).injective

/-- A section of `𝒜|_{U_Zar}` killed by `𝒜|_{U_Zar} ⟶ 𝒪_U` comes from a unique section of the
kernel. -/
theorem chartι_exact (V : (Opens (chartScheme U))ᵒᵖ) (a : (E.chartSheaf U).presheaf.obj V)
    (ha : (E.chartπ U).hom.app V a = 0) : ∃! x, E.chartι U V x = a := by
  obtain ⟨x, hx, hu⟩ := E.exact_kernel _ a ((E.chartπ_eq_zero_iff U V a).1 ha)
  exact ⟨ULift.up x, hx, fun y hy => congrArg ULift.up (hu y.down hy)⟩

/-- The product of two sections of the kernel over the chart is zero. -/
theorem chartι_mul (V : (Opens (chartScheme U))ᵒᵖ) (x y : (E.chartKernel U).val.obj V) :
    E.chartι U V x * E.chartι U V y = 0 :=
  E.square_zero _ x.down y.down

/-- The action of `𝒪_U` on the kernel over the chart is that of `𝒪_X` on `ℐ` over the chart. -/
theorem chartKernel_smul (V : (Opens (chartScheme U))ᵒᵖ)
    (o : (chartScheme U).ringCatSheaf.obj.obj V) (x : (E.chartKernel U).val.obj V) :
    (((E.chartKernel U).val.obj V).smul o).hom x =
      ULift.up ((((E.I.val.obj ((chartOpens B S hS U).op.obj V)).smul
        ((chartRestrictionRingHom B S hS X.2 U).app V o)).hom x.down)) :=
  rfl

/-- `AlgebraicGeometry.Space.chartRestrictionRingHom` carries the image of a section under
`𝒜|_{U_Zar} ⟶ 𝒪_U` to its image under `𝒜 ⟶ 𝒪_X`. -/
theorem chartRestrictionRingHom_chartπ (V : (Opens (chartScheme U))ᵒᵖ)
    (a : (E.chartSheaf U).presheaf.obj V) :
    (chartRestrictionRingHom B S hS X.2 U).app V ((E.chartπ U).hom.app V a) =
      E.π.hom.app ((chartOpens B S hS U).op.obj V) a :=
  (chartΓEquiv U V).symm_apply_apply _

/-- The inclusion of the kernel over the chart is linear over `𝒜|_{U_Zar}`. -/
theorem chartι_smul (V : (Opens (chartScheme U))ᵒᵖ) (a : (E.chartSheaf U).presheaf.obj V)
    (x : (E.chartKernel U).val.obj V) :
    E.chartι U V ((((E.chartKernel U).val.obj V).smul ((E.chartπ U).hom.app V a)).hom x) =
      a * E.chartι U V x := by
  have h := E.smul_lift ((chartOpens B S hS U).op.obj V) a x.down
  rwa [← E.chartRestrictionRingHom_chartπ U V a] at h

/-- **`𝒜|_{U_Zar} ⟶ 𝒪_U` is locally surjective.** -/
theorem isLocallySurjective_chartπ : TopCat.Presheaf.IsLocallySurjective (E.chartπ U).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro V t x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    (chartScheme U).isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  refine ⟨W, hWV, ?_, hxW⟩
  have hA : IsAffineChart B S hS X.1 ((chartOpens B S hS U).obj W) := hW
  obtain ⟨s, hs⟩ := E.surjective_π_app_of_isAffineChart _ hA
    ((chartΓEquiv U (op W)).symm (TopCat.Presheaf.restrictOpen t W hWV))
  exact ⟨s, (congrArg (chartΓEquiv U (op W)) hs).trans (RingEquiv.apply_symm_apply _ _)⟩

/-- The square of a section of `𝒜|_{U_Zar}` killed by the surjection is zero. -/
theorem chart_mul_self_eq_zero (V : (Opens (chartScheme U))ᵒᵖ)
    (a : (E.chartSheaf U).presheaf.obj V) (ha : (E.chartπ U).hom.app V a = 0) : a * a = 0 := by
  obtain ⟨y, rfl, -⟩ := E.chartι_exact U V a ha
  exact E.chartι_mul U V y y

/-- **The square-zero extension `𝒜|_{U_Zar}` of `𝒪_U`, over `Spec ℤ`**, for an étale chart `U`
of `X`: the restriction of the extension sheaf, of the surjection and of the quasi-coherent
kernel to the Zariski opens of `U` (Descent, Proposition 35.9.4 for the kernel). -/
def chartExtension :
    Stacks.Thickenings.SquareZeroExtension (specULiftZIsTerminal.from (chartScheme U)) :=
  Scheme.squareZeroExtensionOverSpecZ (E.chartSheaf U) (E.chartπ U)
    (E.isLocallySurjective_chartπ U) (E.chart_mul_self_eq_zero U) (E.chartKernel U)
    (isQuasicoherent_chartRestrictionSheaf B S hS X E.I E.quasicoherent U) (E.chartι U)
    (E.chartι_naturality U) (E.chartπ_chartι U) (E.chartι_exact U) (E.chartι_smul U)
    (E.chartι_mul U)

/-- **The chart thickening `U'`** of an étale chart `U` of `X`: the scheme with the underlying
space of `U` and structure sheaf `𝒜|_{U_Zar}` on the nose. -/
abbrev chartRealizedScheme : Scheme.{u} :=
  Scheme.realizedScheme (E.chartExtension U)

/-- The inclusion `U ⟶ U'` of an étale chart into its chart thickening. -/
abbrev chartInclusion : chartScheme U ⟶ E.chartRealizedScheme U :=
  Scheme.realizedInclusion (E.chartExtension U)

/-- **`U ⟶ U'` is a first-order thickening.** -/
theorem isFirstOrderThickening_chartInclusion :
    Stacks.Thickenings.IsFirstOrderThickening (E.chartInclusion U) :=
  Scheme.isFirstOrderThickening_realizedInclusion (E.chartExtension U)

/-- The sections of `𝒪_{U'}` over an open `V` are the sections of `𝒜` over the chart `V` cuts
out, on the nose. -/
theorem chartRealizedScheme_presheaf_obj (V : (Opens (chartScheme U))ᵒᵖ) :
    (E.chartRealizedScheme U).presheaf.obj V = E.A.val.obj ((chartOpens B S hS U).op.obj V) :=
  rfl

end AlgebraicGeometry.Space.SquareZeroExtension

end
