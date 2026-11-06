module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionShortExact
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# The thickening of an arbitrary étale chart by a square-zero extension

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`.  The proof of
[Stacks Project, Tag 05ZT] extends the affine construction `U ↦ Spec(𝒜(U))` to *every* object
`V` of the small étale site of `X`: the restriction of `𝒜` to the Zariski site of the scheme of
`V` is a square-zero extension of `𝒪_V` with quasi-coherent kernel, so it is realized by a
first-order thickening `V ⊂ V'` of schemes (More on Morphisms, [Stacks Project, Tag 05YV]).
This file carries out that step.  It is needed because the relation scheme `R = U ×_X U` of a
presentation is not affine in general.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartZariskiSheaf`,
  `…chartZariskiπ`, `…chartZariskiIdeal`: the restrictions of `𝒜`, of the reduction and of `ℐ`
  to the Zariski site of the scheme of an étale chart `V`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartSchemeExtension`: these, as a square-zero
  extension of `𝒪_V` in the sense of `Stacks.Thickenings.SquareZeroExtension`, over the
  terminal scheme `Spec ℤ`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickenedLRS`: the locally ringed space with
  the points of `V` and the restricted extension sheaf.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickening`: **the scheme `V'`**, whose
  underlying locally ringed space is `chartThickenedLRS` on the nose; and
  `…chartImmersion : V ⟶ V'`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.isLocallySurjective_chartZariskiπ`: the
  restricted reduction is locally surjective, since the reduction is surjective over affine
  objects (the first step of the source's proof).
* `AlgebraicGeometry.Space.SquareZeroExtension.isQuasicoherent_chartZariskiIdeal`: the restricted
  kernel is quasi-coherent (Descent, [Stacks Project, Tag 03LC]).
* `AlgebraicGeometry.Space.SquareZeroExtension.isFirstOrderThickening_chartImmersion`:
  **`V ⊂ V'` is a first-order thickening of schemes.**

## Implementation notes

`V'` is defined as the locally ringed space `chartThickenedLRS`, made a scheme through the
isomorphism with the ambient scheme of the realization of Tag 05YV, rather than as that ambient
scheme itself.  This makes its structure sheaf the restricted extension sheaf by definition, so
that morphisms between thickened charts can be written down as morphisms of locally ringed
spaces whose sheaf components are the restriction maps of `𝒜`.

No `@[stacks]` attribute: this is one step of the proof of Tag 05ZT.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- The extension sheaf restricted to the Zariski site of the scheme of an étale chart. -/
def chartZariskiSheaf (V : SmallEtale B S hS X.1) :
    TopCat.Sheaf CommRingCat.{u} (chartScheme V) :=
  haveI := isContinuous_openChartFunctor B S hS X V
  ((openChartFunctor B S hS X.1 V).sheafPushforwardContinuous CommRingCat.{u}
    (Opens.grothendieckTopology (chartScheme V)) (SmallEtale.topology B S hS X.1)).obj E.A

/-- Sections of the restricted extension sheaf over an open `W` of the chart are sections of
`E.A` over the image of `W` in the small étale site. -/
theorem chartZariskiSheaf_obj (V : SmallEtale B S hS X.1) (W : (chartScheme V).Opens) :
    (chartZariskiSheaf B S hS E V).obj.obj (op W) =
      E.A.obj.obj (op ((openChartFunctor B S hS X.1 V).obj W)) := rfl

/-- The reduction, restricted to the Zariski site of a chart. -/
def chartZariskiπ (V : SmallEtale B S hS X.1) :
    chartZariskiSheaf B S hS E V ⟶ (chartScheme V).sheaf :=
  ⟨Functor.whiskerLeft (openChartFunctor B S hS X.1 V).op E.π.hom ≫
    (Scheme.restrictFunctorΓ (X := chartScheme V)).hom⟩

/-- The reduction on the Zariski restriction, over an open, is `E.π` over the corresponding chart
followed by the identification of global functions of the open subscheme with sections. -/
theorem chartZariskiπ_app (V : SmallEtale B S hS X.1) (W : (chartScheme V).Opens)
    (a : (chartZariskiSheaf B S hS E V).obj.obj (op W)) :
    (chartZariskiπ B S hS E V).hom.app (op W) a =
      (Scheme.restrictFunctorΓ (X := chartScheme V)).hom.app (op W)
        (E.π.hom.app (op ((openChartFunctor B S hS X.1 V).obj W)) a) := rfl

/-- **The reduction on the Zariski restriction is locally surjective**: over an affine open the
reduction of the extension is surjective on sections, and the affine opens form a basis. -/
theorem isLocallySurjective_chartZariskiπ (V : SmallEtale B S hS X.1) :
    TopCat.Presheaf.IsLocallySurjective (chartZariskiπ B S hS E V).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W t x hx
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hW'W⟩ :=
    (chartScheme V).isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  refine ⟨W', hW'W, ?_, hxW'⟩
  have haff : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((openChartFunctor B S hS X.1 V).obj W')) := hW'
  obtain ⟨s, hs⟩ := SquareZeroExtension.surjective_π_app_of_isAffine B S hS E _ haff
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op W')
      ((chartScheme V).presheaf.map (homOfLE hW'W).op t))
  refine ⟨s, (chartZariskiπ_app B S hS E V W' s).trans ?_⟩
  rw [hs]
  exact ConcreteCategory.congr_hom
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).inv_hom_id_app (op W')) _

/-- A surjective ring map onto a local ring whose kernel consists of elements of square zero
reflects units. -/
theorem isUnit_of_isUnit_map_of_surjective_of_sq_eq_zero {R T : Type*} [CommRing R]
    [CommRing T] (g : R →+* T) (hg : Function.Surjective g)
    (hker : ∀ r ∈ RingHom.ker g, r ^ 2 = 0) {a : R} (ha : IsUnit (g a)) : IsUnit a := by
  obtain ⟨b', hb'⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hg b'
  have hk : a * b - 1 ∈ RingHom.ker g := by
    rw [RingHom.mem_ker, map_sub, map_mul, hb', map_one, sub_self]
  have hnil : IsNilpotent (a * b - 1) := ⟨2, hker _ hk⟩
  exact isUnit_of_mul_isUnit_left (by simpa using hnil.isUnit_one_add)

/-- A ring with a surjection onto a local ring whose kernel consists of elements of square zero is
local. -/
theorem isLocalRing_of_surjective_of_sq_eq_zero {R T : Type*} [CommRing R] [CommRing T]
    [hT : IsLocalRing T] (g : R →+* T) (hg : Function.Surjective g)
    (hker : ∀ r ∈ RingHom.ker g, r ^ 2 = 0) : IsLocalRing R := by
  have : Nontrivial R := hg.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab => ?_
  have hab' : IsUnit (g a + g b) := by simpa only [map_add] using hab.map g
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hab').imp
    (isUnit_of_isUnit_map_of_surjective_of_sq_eq_zero g hg hker)
    (isUnit_of_isUnit_map_of_surjective_of_sq_eq_zero g hg hker)

/-- The stalk map of the reduction on the Zariski restriction is surjective. -/
theorem surjective_stalkMap_chartZariskiπ (V : SmallEtale B S hS X.1) (x : chartScheme V) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom).hom :=
  (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp
    (isLocallySurjective_chartZariskiπ B S hS E V) x

/-- The reduction on the Zariski restriction detects zero. -/
private theorem eq_zero_of_chartZariskiπ_app_eq_zero_aux (V : SmallEtale B S hS X.1)
    (W : (chartScheme V).Opens) (a : (chartZariskiSheaf B S hS E V).obj.obj (op W))
    (ha : (chartZariskiπ B S hS E V).hom.app (op W) a = 0) :
    E.π.hom.app (op ((openChartFunctor B S hS X.1 V).obj W)) a = 0 :=
  (ConcreteCategory.congr_hom
    ((Scheme.restrictFunctorΓ (X := chartScheme V)).hom_inv_id_app (op W)) _).symm.trans
    ((congrArg ((Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op W)) ha).trans
      (map_zero _))

/-- An element of the kernel of the reduction over an open is the image of a section of `ℐ`. -/
theorem sq_eq_zero_of_chartZariskiπ_app_eq_zero (V : SmallEtale B S hS X.1)
    (W : (chartScheme V).Opens) (a : (chartZariskiSheaf B S hS E V).obj.obj (op W))
    (ha : (chartZariskiπ B S hS E V).hom.app (op W) a = 0) : a ^ 2 = 0 := by
  have ha' := eq_zero_of_chartZariskiπ_app_eq_zero_aux B S hS E V W a ha
  obtain ⟨z, hz, -⟩ := E.exact_kernel _ a ha'
  rw [← hz]
  exact (pow_two _).trans (E.square_zero _ z z)

/-- The kernel of the stalk map of the reduction on the Zariski restriction consists of elements
of square zero. -/
theorem sq_eq_zero_of_mem_ker_stalkMap_chartZariskiπ (V : SmallEtale B S hS X.1)
    (x : chartScheme V) :
    ∀ r ∈ RingHom.ker
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom).hom,
      r ^ 2 = 0 := by
  intro r hr
  obtain ⟨W, hxW, a, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq (chartZariskiSheaf B S hS E V).obj r
  have hr0 := RingHom.mem_ker.mp hr
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hr0
  have hzero : TopCat.Presheaf.germ (chartScheme V).presheaf W x hxW
      ((chartZariskiπ B S hS E V).hom.app (op W) a) =
      TopCat.Presheaf.germ (chartScheme V).presheaf W x hxW 0 := by
    rwa [map_zero]
  obtain ⟨W', hxW', i₁, i₂, hres⟩ :=
    TopCat.Presheaf.germ_eq (chartScheme V).presheaf x hxW hxW _ _ hzero
  have ha : (chartZariskiπ B S hS E V).hom.app (op W')
      ((chartZariskiSheaf B S hS E V).obj.map i₁.op a) = 0 :=
    (ConcreteCategory.congr_hom ((chartZariskiπ B S hS E V).hom.naturality i₁.op) a).trans
      (hres.trans (map_zero _))
  calc (TopCat.Presheaf.germ (chartZariskiSheaf B S hS E V).obj W x hxW a) ^ 2
      = (TopCat.Presheaf.germ (chartZariskiSheaf B S hS E V).obj W' x hxW'
          ((chartZariskiSheaf B S hS E V).obj.map i₁.op a)) ^ 2 := by
        rw [TopCat.Presheaf.germ_res_apply]
    _ = TopCat.Presheaf.germ (chartZariskiSheaf B S hS E V).obj W' x hxW'
          (((chartZariskiSheaf B S hS E V).obj.map i₁.op a) ^ 2) := (map_pow _ _ _).symm
    _ = 0 := by rw [sq_eq_zero_of_chartZariskiπ_app_eq_zero B S hS E V W' _ ha, map_zero]

/-- The stalk map of the reduction on the Zariski restriction reflects units. -/
theorem isLocalHom_stalkMap_chartZariskiπ (V : SmallEtale B S hS X.1) (x : chartScheme V) :
    IsLocalHom
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom).hom :=
  ⟨fun _ ha => isUnit_of_isUnit_map_of_surjective_of_sq_eq_zero _
    (surjective_stalkMap_chartZariskiπ B S hS E V x)
    (sq_eq_zero_of_mem_ker_stalkMap_chartZariskiπ B S hS E V x) ha⟩

/-- The sheafed space with the topology of the chart and the restricted extension sheaf. -/
abbrev chartThickenedSpace (V : SmallEtale B S hS X.1) : SheafedSpace CommRingCat.{u} :=
  Stacks.Thickenings.thickenedSpace (chartScheme V) (chartZariskiSheaf B S hS E V)

/-- **The thickened chart is a locally ringed space**: its stalks surject onto the local stalks
of the chart scheme with a kernel of square-zero elements. -/
def chartThickenedLRS (V : SmallEtale B S hS X.1) : LocallyRingedSpace.{u} where
  toSheafedSpace := chartThickenedSpace B S hS E V
  isLocalRing x :=
    isLocalRing_of_surjective_of_sq_eq_zero
      (hT := (chartScheme V).toLocallyRingedSpace.isLocalRing x) _
      (surjective_stalkMap_chartZariskiπ B S hS E V x)
      (sq_eq_zero_of_mem_ker_stalkMap_chartZariskiπ B S hS E V x)

/-- The inclusion of a chart into its thickened sheafed space: the identity on points and the
reduction on sections. -/
def chartZariskiInclusion (V : SmallEtale B S hS X.1) :
    (chartScheme V).toSheafedSpace ⟶ chartThickenedSpace B S hS E V :=
  InducedCategory.homMk { base := 𝟙 _, c := (chartZariskiπ B S hS E V).hom }

/-- The stalk map of the inclusion of a chart into its thickened sheafed space at `x` is the
stalk at `x` of the reduction. -/
theorem chartZariskiInclusion_stalkMap (V : SmallEtale B S hS X.1) (x : chartScheme V) :
    (chartZariskiInclusion B S hS E V).hom.stalkMap x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom := by
  show (TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom ≫
      TopCat.Presheaf.stalkPushforward CommRingCat (𝟙 (chartScheme V : TopCat))
        (chartScheme V).presheaf x =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom
  rw [TopCat.Presheaf.stalkPushforward.id]
  show (TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (TopCat.Presheaf.Pushforward.id (chartScheme V).presheaf).hom =
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map (chartZariskiπ B S hS E V).hom
  refine Eq.trans ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp
    (chartZariskiπ B S hS E V).hom
      (TopCat.Presheaf.Pushforward.id (chartScheme V).presheaf).hom).symm ?_
  congr 1

/-- The inclusion of a chart into its thickened locally ringed space. -/
def chartZariskiInclusionLRS (V : SmallEtale B S hS X.1) :
    (chartScheme V).toLocallyRingedSpace ⟶ chartThickenedLRS B S hS E V :=
  LocallyRingedSpace.homMk (X := (chartScheme V).toLocallyRingedSpace)
    (Y := chartThickenedLRS B S hS E V) (chartZariskiInclusion B S hS E V) fun x => by
    change IsLocalHom ((chartZariskiInclusion B S hS E V).hom.stalkMap x).hom
    rw [chartZariskiInclusion_stalkMap]
    exact isLocalHom_stalkMap_chartZariskiπ B S hS E V x

/-- The structure morphism of the thickened chart to `Spec ℤ`, as a morphism of locally ringed
spaces. -/
def chartThickenedToSpecZ (V : SmallEtale B S hS X.1) :
    chartThickenedLRS B S hS E V ⟶ (Spec (CommRingCat.of (ULift.{u} ℤ))).toLocallyRingedSpace :=
  LocallyRingedSpace.toΓSpec (chartThickenedLRS B S hS E V) ≫
    Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom))

/-- The inclusion of a chart into its thickened locally ringed space, followed by the structure
morphism to `Spec ℤ`, is the structure morphism of the chart. -/
theorem chartZariskiInclusionLRS_comp_chartThickenedToSpecZ (V : SmallEtale B S hS X.1) :
    chartZariskiInclusionLRS B S hS E V ≫ chartThickenedToSpecZ B S hS E V =
      (specULiftZIsTerminal.from (chartScheme V)).toLRSHom :=
  congrArg Scheme.Hom.toLRSHom (specULiftZIsTerminal.hom_ext
    (Scheme.Hom.mk (chartZariskiInclusionLRS B S hS E V ≫ chartThickenedToSpecZ B S hS E V)) _)

/-- The kernel `ℐ` restricted to the Zariski site of the scheme of an étale chart. -/
def chartZariskiIdeal (V : SmallEtale B S hS X.1) : (chartScheme V).Modules :=
  haveI := isContinuous_openChartFunctor B S hS X V
  (SheafOfModules.pushforward.{u} (chartSchemeRestrictionSheafHom B S hS X.2 V)).obj E.I

/-- The restricted kernel is quasi-coherent. -/
theorem isQuasicoherent_chartZariskiIdeal (V : SmallEtale B S hS X.1) :
    (chartZariskiIdeal B S hS E V).IsQuasicoherent :=
  have := isContinuous_openChartFunctor B S hS X V
  (SheafOfModules.isQuasicoherent _).prop_of_iso
    (restrictToChartSchemeIsoPushforward B S hS X.2 V E.I)
    (isQuasicoherent_restrictToChartScheme B S hS X E.I E.quasicoherent V)

/-- The reduction on the Zariski restriction detects zero. -/
theorem eq_zero_of_chartZariskiπ_app_eq_zero (V : SmallEtale B S hS X.1)
    (W : (chartScheme V).Opens) (a : (chartZariskiSheaf B S hS E V).obj.obj (op W))
    (ha : (chartZariskiπ B S hS E V).hom.app (op W) a = 0) :
    E.π.hom.app (op ((openChartFunctor B S hS X.1 V).obj W)) a = 0 :=
  eq_zero_of_chartZariskiπ_app_eq_zero_aux B S hS E V W a ha

/-- **The restriction of a square-zero extension of `𝒪_X` to the Zariski site of an étale chart
`V` is a square-zero extension of `𝒪_V` in the sense of the scheme-level datum**, over the
terminal scheme `Spec ℤ`. -/
def chartSchemeExtension (V : SmallEtale B S hS X.1) :
    Stacks.Thickenings.SquareZeroExtension (specULiftZIsTerminal.from (chartScheme V)) where
  A := chartZariskiSheaf B S hS E V
  π := chartZariskiπ B S hS E V
  locallySurjective_π := isLocallySurjective_chartZariskiπ B S hS E V
  inclusion := chartZariskiInclusion B S hS E V
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := (chartThickenedToSpecZ B S hS E V).toShHom
  over_base := congrArg LocallyRingedSpace.Hom.toShHom
    (chartZariskiInclusionLRS_comp_chartThickenedToSpecZ B S hS E V)
  I := chartZariskiIdeal B S hS E V
  quasicoherent := isQuasicoherent_chartZariskiIdeal B S hS E V
  ι W := E.ι (op ((openChartFunctor B S hS X.1 V).obj W.unop))
  naturality g x := E.naturality ((openChartFunctor B S hS X.1 V).op.map g) x
  mem_kernel W x := by
    change (Scheme.restrictFunctorΓ (X := chartScheme V)).hom.app W
      (E.π.hom.app (op ((openChartFunctor B S hS X.1 V).obj W.unop)) (E.ι _ x)) = 0
    exact (congrArg _ (E.mem_kernel _ x)).trans (map_zero _)
  exact_kernel W a ha :=
    E.exact_kernel _ a (eq_zero_of_chartZariskiπ_app_eq_zero B S hS E V W.unop a ha)
  smul_lift W a x := by
    refine Eq.trans ?_ (E.smul_lift (op ((openChartFunctor B S hS X.1 V).obj W.unop)) a x)
    congr 1
    exact congrArg (fun r => ((E.I.val.obj (op ((openChartFunctor B S hS X.1 V).obj W.unop))).smul
        r).asHom x)
      (ConcreteCategory.congr_hom
        ((Scheme.restrictFunctorΓ (X := chartScheme V)).hom_inv_id_app W) _)
  square_zero W x y := E.square_zero _ x y

/-- A realization of the restricted extension over a chart, by [Stacks Project, Tag 05YV]. -/
def chartRealization (V : SmallEtale B S hS X.1) :
    Stacks.Thickenings.Realization (chartSchemeExtension B S hS E V) :=
  (Stacks.Thickenings.squareZeroExtension_realization (chartSchemeExtension B S hS E V)).some

/-- The ambient scheme of the realization is isomorphic, as a locally ringed space, to the
thickened chart. -/
def chartAmbientIso (V : SmallEtale B S hS X.1) :
    (chartRealization B S hS E V).ambient.toLocallyRingedSpace ≅ chartThickenedLRS B S hS E V :=
  LocallyRingedSpace.isoOfSheafedSpaceIso (chartRealization B S hS E V).sheafedIso

/-- **The thickened chart `V'`**: the locally ringed space with the points of the chart `V` and
the restricted extension sheaf as structure sheaf, which is a scheme because it is isomorphic to
the ambient scheme of [Stacks Project, Tag 05YV]. -/
def chartThickening (V : SmallEtale B S hS X.1) : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (chartThickenedLRS B S hS E V) fun x => by
    let e := chartAmbientIso B S hS E V
    let Z := (chartRealization B S hS E V).ambient
    obtain ⟨i, y, hy⟩ := Z.affineCover.exists_eq (e.inv.base x)
    have hi : LocallyRingedSpace.IsOpenImmersion (Z.affineCover.f i).toLRSHom :=
      inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (Z.affineCover.f i))
    refine ⟨_, (Z.affineCover.f i).toLRSHom ≫ e.hom, ⟨y, ?_⟩,
      LocallyRingedSpace.IsOpenImmersion.comp (H := hi) _ e.hom⟩
    change e.hom.base ((Z.affineCover.f i).base y) = x
    rw [hy]
    change (e.inv ≫ e.hom).base x = x
    rw [e.inv_hom_id]
    rfl

/-- The underlying locally ringed space of the thickened chart is `chartThickenedLRS`. -/
theorem chartThickening_toLocallyRingedSpace (V : SmallEtale B S hS X.1) :
    (chartThickening B S hS E V).toLocallyRingedSpace = chartThickenedLRS B S hS E V := rfl

/-- The inclusion `V ⟶ V'` of a chart into its thickening. -/
def chartImmersion (V : SmallEtale B S hS X.1) : chartScheme V ⟶ chartThickening B S hS E V :=
  Scheme.Hom.mk (chartZariskiInclusionLRS B S hS E V)

/-- The ambient scheme of the realization is isomorphic, as a scheme, to the thickened chart. -/
def chartAmbientSchemeIso (V : SmallEtale B S hS X.1) :
    (chartRealization B S hS E V).ambient ≅ chartThickening B S hS E V where
  hom := Scheme.Hom.mk (chartAmbientIso B S hS E V).hom
  inv := Scheme.Hom.mk (chartAmbientIso B S hS E V).inv
  hom_inv_id := Scheme.Hom.ext' (chartAmbientIso B S hS E V).hom_inv_id
  inv_hom_id := Scheme.Hom.ext' (chartAmbientIso B S hS E V).inv_hom_id

/-- The immersion of the realization followed by the isomorphism of its ambient scheme with the
thickened chart is the inclusion `chartImmersion`. -/
theorem immersion_comp_chartAmbientSchemeIso (V : SmallEtale B S hS X.1) :
    (chartRealization B S hS E V).immersion ≫ (chartAmbientSchemeIso B S hS E V).hom =
      chartImmersion B S hS E V :=
  Scheme.Hom.ext' (LocallyRingedSpace.forgetToSheafedSpace.map_injective
    (chartRealization B S hS E V).inclusion_eq)

/-- **The inclusion of a chart into its thickening is a first-order thickening.** -/
theorem isFirstOrderThickening_chartImmersion (V : SmallEtale B S hS X.1) :
    Stacks.Thickenings.IsFirstOrderThickening (chartImmersion B S hS E V) := by
  have h : IsPullback (chartImmersion B S hS E V) (𝟙 _)
      (chartAmbientSchemeIso B S hS E V).inv (chartRealization B S hS E V).immersion :=
    IsPullback.of_vert_isIso ⟨by
      rw [Category.id_comp, ← immersion_comp_chartAmbientSchemeIso, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]⟩
  exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback h
    (chartRealization B S hS E V).immersion_isFirstOrder

end SquareZeroExtension

end AlgebraicGeometry.Space

end
