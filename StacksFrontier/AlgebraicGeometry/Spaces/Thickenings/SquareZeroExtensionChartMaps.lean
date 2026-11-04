module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FMapGlobalSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartThickening

/-!
# Morphisms between the thickenings realizing square-zero extensions

Let `X₁ ⟶ X₂` be a morphism of schemes and let `𝒜ᵢ ⟶ 𝒪_{Xᵢ}` be locally surjective maps of sheaves
of rings killing only sections of square zero. A map of sheaves of rings `c : 𝒜₂ ⟶ f_*𝒜₁` lifting
`f♯` is a morphism of locally ringed spaces `(X₁, 𝒜₁) ⟶ (X₂, 𝒜₂)` over `f`: its stalk maps are
local because, composed with the local surjection `𝒜₁,ₓ ⟶ 𝒪_{X₁,x}`, they become the local map
`𝒜₂,f(x) ⟶ 𝒪_{X₂,f(x)} ⟶ 𝒪_{X₁,x}`.

## Main definitions

* `AlgebraicGeometry.Scheme.thickenedMap`: the morphism of locally ringed spaces over `f` given by
  `c`.
* `AlgebraicGeometry.Scheme.realizedMap`: the same morphism between the schemes realizing two
  square-zero extensions (`AlgebraicGeometry.Scheme.realizedScheme`).
* `AlgebraicGeometry.Scheme.realizedMapTo`: the morphism from the scheme realizing a square-zero
  extension `𝒜₁` of `𝒪_{X₁}` to a scheme `Z` extending `f : X₁ ⟶ Z`, given by `𝒪_Z ⟶ f_*𝒜₁`
  lifting `f♯`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeMap`: the morphism `V' ⟶ U'` of
  chart thickenings of a square-zero extension of the étale structure sheaf over `g`.

## Main results

* `AlgebraicGeometry.Scheme.thickenedShMap_stalkMap_comp`: the square of stalk maps.
* `AlgebraicGeometry.Space.toScheme_map_chartOpensRestrict`: the morphism of schemes underlying
  the restriction `V|_{g⁻¹O} ⟶ U|_O` (`AlgebraicGeometry.Space.chartOpensRestrict`) of a
  morphism of étale charts `g : V ⟶ U` to a Zariski open and its preimage is `g|_O`.
* `AlgebraicGeometry.Scheme.realizedInclusion_comp_realizedMap`: `realizedMap` is a morphism of
  thickenings over `f`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartInclusion_comp_chartRealizedSchemeMap`: so is
  `V' ⟶ U'` over `g`.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

section Map

/-- Restricting a section along `eqToHom rfl` does nothing. -/
private theorem presheaf_map_eqToHom_rfl_apply {X : Scheme.{u}} {U : X.Opens}
    (a : X.presheaf.obj (op U)) : X.presheaf.map (eqToHom (rfl : U = U)).op a = a := by
  simp

variable {X₁ X₂ : Scheme.{u}} (A₁ : TopCat.Sheaf CommRingCat.{u} X₁) (π₁ : A₁ ⟶ X₁.sheaf)
  (hπ₁ : TopCat.Presheaf.IsLocallySurjective π₁.hom)
  (hsq₁ : ∀ (V : (Opens X₁)ᵒᵖ) (a : A₁.presheaf.obj V), π₁.hom.app V a = 0 → a * a = 0)
  (A₂ : TopCat.Sheaf CommRingCat.{u} X₂) (π₂ : A₂ ⟶ X₂.sheaf)
  (hπ₂ : TopCat.Presheaf.IsLocallySurjective π₂.hom)
  (hsq₂ : ∀ (V : (Opens X₂)ᵒᵖ) (a : A₂.presheaf.obj V), π₂.hom.app V a = 0 → a * a = 0)
  (f : X₁ ⟶ X₂) (c : A₂.presheaf ⟶ f.base _* A₁.presheaf)
  (hc : ∀ (O : X₂.Opens) (a : A₂.presheaf.obj (op O)),
    π₁.hom.app (op (f ⁻¹ᵁ O)) (c.app (op O) a) = f.app O (π₂.hom.app (op O) a))

/-- The morphism `(X₁, 𝒜₁) ⟶ (X₂, 𝒜₂)` of sheafed spaces over `f` given by `c`. -/
def thickenedShMap : Stacks.Thickenings.thickenedSpace X₁ A₁ ⟶
    Stacks.Thickenings.thickenedSpace X₂ A₂ :=
  InducedCategory.homMk { base := f.base, c := c }

include hc in
/-- The stalk map of `thickenedShMap` at `x`, followed by `𝒜₁,ₓ ⟶ 𝒪_{X₁,x}`, is
`𝒜₂,f(x) ⟶ 𝒪_{X₂,f(x)}` followed by the stalk map of `f`. -/
theorem thickenedShMap_stalkMap_comp (x : X₁) :
    (thickenedShMap A₁ A₂ f c).hom.stalkMap x ≫ sheafStalkMap A₁ π₁ x =
      sheafStalkMap A₂ π₂ (f x) ≫ f.stalkMap x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro O hxO
  ext a
  show sheafStalkMap A₁ π₁ x ((thickenedShMap A₁ A₂ f c).hom.stalkMap x
      (A₂.presheaf.germ O (f x) hxO a)) =
    f.stalkMap x (sheafStalkMap A₂ π₂ (f x) (A₂.presheaf.germ O (f x) hxO a))
  refine (congrArg (sheafStalkMap A₁ π₁ x)
    (PresheafedSpace.stalkMap_germ_apply (thickenedShMap A₁ A₂ f c).hom O x hxO a)).trans ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (f.stalkMap x)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _)).symm
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f O x hxO _).symm
  exact congrArg _ (hc O a)

/-- The morphism `(X₁, 𝒜₁) ⟶ (X₂, 𝒜₂)` of sheafed spaces over `f` given by a map `c` of
sheaves of rings `𝒜₂ ⟶ f_*𝒜₁`. -/
def thickenedMap : thickenedLocallyRingedSpace A₁ π₁ hπ₁ hsq₁ ⟶
    thickenedLocallyRingedSpace A₂ π₂ hπ₂ hsq₂ :=
  LocallyRingedSpace.homMk (thickenedShMap A₁ A₂ f c) fun x ↦ by
    let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat (f x)).obj A₂.obj) :=
      isLocalRing_stalk_of_squareZero A₂ π₂ hπ₂ hsq₂ (f x)
    let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat (f x)).obj X₂.sheaf.obj) :=
      X₂.toLocallyRingedSpace.isLocalRing (f x)
    have h2 : IsLocalHom (sheafStalkMap A₂ π₂ (f x)).hom := IsLocalHom.of_surjective _
      ((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks π₂.hom).1 hπ₂ (f x))
    have h3 : IsLocalHom ((sheafStalkMap A₁ π₁ x).hom.comp
        ((thickenedShMap A₁ A₂ f c).hom.stalkMap x).hom) := by
      change IsLocalHom ((thickenedShMap A₁ A₂ f c).hom.stalkMap x ≫ sheafStalkMap A₁ π₁ x).hom
      rw [thickenedShMap_stalkMap_comp A₁ π₁ A₂ π₂ f c hc x]
      change IsLocalHom ((f.stalkMap x).hom.comp (sheafStalkMap A₂ π₂ (f x)).hom)
      exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _ (f.toLRSHom.prop x) h2
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ h3

end Map

section RealizedMap

variable {X₁ X₂ T₁ T₂ : Scheme.{u}} {g₁ : X₁ ⟶ T₁} {g₂ : X₂ ⟶ T₂}
  (E₁ : Stacks.Thickenings.SquareZeroExtension g₁) (E₂ : Stacks.Thickenings.SquareZeroExtension g₂)
  (f : X₁ ⟶ X₂) (c : E₂.A.presheaf ⟶ f.base _* E₁.A.presheaf)
  (hc : ∀ (O : X₂.Opens) (a : E₂.A.presheaf.obj (op O)),
    E₁.π.hom.app (op (f ⁻¹ᵁ O)) (c.app (op O) a) = f.app O (E₂.π.hom.app (op O) a))

/-- **The morphism of realized thickenings over `f : X₁ ⟶ X₂`** given by a map `c : 𝒜₂ ⟶ f_*𝒜₁`
lifting `f♯`: it is the identity of `f` on spaces and `c` on sections. -/
def realizedMap : realizedScheme E₁ ⟶ realizedScheme E₂ :=
  Scheme.Hom.mk (thickenedMap E₁.A E₁.π E₁.locallySurjective_π
    (squareZeroExtension_mul_self_eq_zero E₁) E₂.A E₂.π E₂.locallySurjective_π
    (squareZeroExtension_mul_self_eq_zero E₂) f c hc)

/-- On sections over `O`, `realizedMap` is `c`. -/
theorem realizedMap_app (O : (realizedScheme E₂).Opens) :
    (realizedMap E₁ E₂ f c hc).app O = c.app (op O) :=
  rfl

/-- `realizedMap` is a morphism of thickenings over `f`. -/
theorem realizedInclusion_comp_realizedMap :
    realizedInclusion E₁ ≫ realizedMap E₁ E₂ f c hc = f ≫ realizedInclusion E₂ :=
  Scheme.Hom.ext rfl fun O ↦ by
    ext a
    exact (presheaf_map_eqToHom_rfl_apply _).trans (hc O a)

end RealizedMap

section RealizedMapTo

variable {X₁ T₁ Z : Scheme.{u}} {g₁ : X₁ ⟶ T₁} (E₁ : Stacks.Thickenings.SquareZeroExtension g₁)
  (f : X₁ ⟶ Z) (c : Z.presheaf ⟶ f.base _* E₁.A.presheaf)
  (hc : ∀ (O : Z.Opens) (a : Z.presheaf.obj (op O)),
    E₁.π.hom.app (op (f ⁻¹ᵁ O)) (c.app (op O) a) = f.app O a)

/-- The morphism `(X₁, 𝒜₁) ⟶ Z` of sheafed spaces over `f` given by `c : 𝒪_Z ⟶ f_*𝒜₁`. -/
def realizedShMapTo : Stacks.Thickenings.thickenedSpace X₁ E₁.A ⟶ Z.toSheafedSpace :=
  InducedCategory.homMk { base := f.base, c := c }

include hc in
/-- The stalk map of `realizedShMapTo` at `x`, followed by `𝒜₁,ₓ ⟶ 𝒪_{X₁,x}`, is the stalk map
of `f`. -/
theorem realizedShMapTo_stalkMap_comp (x : X₁) :
    (realizedShMapTo E₁ f c).hom.stalkMap x ≫ sheafStalkMap E₁.A E₁.π x = f.stalkMap x := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro O hxO
  ext a
  show sheafStalkMap E₁.A E₁.π x ((realizedShMapTo E₁ f c).hom.stalkMap x
      (Z.presheaf.germ O (f x) hxO a)) = f.stalkMap x (Z.presheaf.germ O (f x) hxO a)
  refine (congrArg (sheafStalkMap E₁.A E₁.π x)
    (PresheafedSpace.stalkMap_germ_apply (realizedShMapTo E₁ f c).hom O x hxO a)).trans ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap_apply f O x hxO _).symm
  exact congrArg _ (hc O a)

/-- **The morphism from a realized thickening to a scheme `Z`** extending `f : X₁ ⟶ Z`, given by
a map `c : 𝒪_Z ⟶ f_*𝒜₁` lifting `f♯`: it is `f` on spaces and `c` on sections. -/
def realizedMapTo : realizedScheme E₁ ⟶ Z :=
  Scheme.Hom.mk (LocallyRingedSpace.homMk (realizedShMapTo E₁ f c) fun x ↦ by
    let : IsLocalRing ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj E₁.A.obj) :=
      isLocalRing_stalk_of_squareZero E₁.A E₁.π E₁.locallySurjective_π
        (squareZeroExtension_mul_self_eq_zero E₁) x
    have h3 : IsLocalHom ((sheafStalkMap E₁.A E₁.π x).hom.comp
        ((realizedShMapTo E₁ f c).hom.stalkMap x).hom) := by
      change IsLocalHom ((realizedShMapTo E₁ f c).hom.stalkMap x ≫ sheafStalkMap E₁.A E₁.π x).hom
      rw [realizedShMapTo_stalkMap_comp E₁ f c hc x]
      exact f.toLRSHom.prop x
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ h3)

/-- On spaces, `realizedMapTo` is `f`. -/
theorem realizedMapTo_base : (realizedMapTo E₁ f c hc).base = f.base :=
  rfl

/-- On sections over `O`, `realizedMapTo` is `c`. -/
theorem realizedMapTo_app (O : Z.Opens) : (realizedMapTo E₁ f c hc).app O = c.app (op O) :=
  rfl

/-- `realizedMapTo` extends `f`. -/
theorem realizedInclusion_comp_realizedMapTo : realizedInclusion E₁ ≫ realizedMapTo E₁ f c hc = f :=
  Scheme.Hom.ext rfl fun O ↦ by
    ext a
    exact (presheaf_map_eqToHom_rfl_apply _).trans (hc O a)

end RealizedMapTo

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism of schemes underlying the restriction `V|_{g⁻¹O} ⟶ U|_O` of a morphism of étale
charts `g : V ⟶ U` is the restriction `g|_O` of the morphism of chart schemes. -/
theorem toScheme_map_chartOpensRestrict {U V : SmallEtale B S hS F} (g : V ⟶ U)
    (O : (chartScheme U).Opens) :
    (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (chartOpensRestrict B S hS g O)) =
      chartSchemeMap g ∣_ O :=
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)
variable {U V : SmallEtale B S hS X.1} (g : V ⟶ U)

/-- The restriction maps of `𝒜` along a morphism of étale charts `g : V ⟶ U`, as a map
`𝒜|_{U_Zar} ⟶ g_*(𝒜|_{V_Zar})`. -/
def chartSheafMap :
    (E.chartSheaf U).presheaf ⟶ (chartSchemeMap g).base _* (E.chartSheaf V).presheaf :=
  Functor.whiskerRight (NatTrans.op (chartOpensRestrictNatTrans B S hS g)) E.A.val

/-- On sections over `O`, `chartSheafMap` is the restriction map of `𝒜` along
`V|_{g⁻¹O} ⟶ U|_O`. -/
theorem chartSheafMap_app (O : (chartScheme U).Opens) :
    (E.chartSheafMap g).app (op O) = E.A.val.map (chartOpensRestrict B S hS g O).op :=
  rfl

/-- `chartSheafMap` lifts the map of structure sheaves of the chart morphism. -/
theorem chartπ_chartSheafMap (O : (chartScheme U).Opens)
    (a : (E.chartSheaf U).presheaf.obj (op O)) :
    (E.chartπ V).hom.app (op (chartSchemeMap g ⁻¹ᵁ O)) ((E.chartSheafMap g).app (op O) a) =
      (chartSchemeMap g).app O ((E.chartπ U).hom.app (op O) a) := by
  rw [chartπ_apply', chartπ_apply', chartSheafMap_app]
  refine (congrArg (chartΓEquiv V (op (chartSchemeMap g ⁻¹ᵁ O)))
    (ConcreteCategory.congr_hom (E.π.hom.naturality (chartOpensRestrict B S hS g O).op) a)).trans ?_
  exact ConcreteCategory.congr_hom (morphismRestrict_appTop_topIso (chartSchemeMap g) O)
    (E.π.hom.app (op ((chartOpens B S hS U).obj O)) a)

/-- **The morphism of chart thickenings `V' ⟶ U'`** over a morphism of étale charts
`g : V ⟶ U`: the morphism `g` on spaces and the restriction maps of `𝒜` on sections. -/
def chartRealizedSchemeMap : E.chartRealizedScheme V ⟶ E.chartRealizedScheme U :=
  Scheme.realizedMap (E.chartExtension V) (E.chartExtension U) (chartSchemeMap g)
    (E.chartSheafMap g) (E.chartπ_chartSheafMap g)

/-- The morphism of chart thickenings is a morphism of thickenings over `g`. -/
theorem chartInclusion_comp_chartRealizedSchemeMap :
    E.chartInclusion V ≫ E.chartRealizedSchemeMap g = chartSchemeMap g ≫ E.chartInclusion U :=
  Scheme.realizedInclusion_comp_realizedMap _ _ _ _ _

end AlgebraicGeometry.Space.SquareZeroExtension

end
