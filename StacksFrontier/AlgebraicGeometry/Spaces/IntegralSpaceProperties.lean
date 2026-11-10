module

public import Mathlib.Algebra.Category.Ring.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedBasicOpenNonempty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Global sections of an integral algebraic space

The global regular functions on an algebraic space `X` over a scheme `S` are the compatible
families of regular functions on the étale charts of `X`, that is the sections of the structure
presheaf `AlgebraicGeometry.Space.structurePresheaf` of the small étale site of `X`. When `X`
is integral in the sense of Stacks 0AD4 this ring is a domain, and when `X` is in addition
normal it is a normal domain.

## Main results

* `AlgebraicGeometry.Space.isDomain_globalSections_of_isIntegralSpace`: the ring of global
  sections of an integral algebraic space is a domain.
* `AlgebraicGeometry.Space.isNormalDomain_globalSections_of_isIntegralSpace`: the ring of global
  sections of a normal integral algebraic space is a normal domain.

## Implementation notes

The small étale site of an algebraic space has no terminal object, so the ring of global
sections is not a value of the structure presheaf. It is `RingCat.sectionsSubring` of the
structure presheaf composed with the forgetful functor to rings: the subring of
`∀ U, Γ(U, 𝒪_U)`, the product over all étale charts `U` of `X`, cut out by compatibility with
every morphism of charts, with the pointwise ring structure.

Normality of `X` is the étale-local scheme property `AlgebraicGeometry.IsNormal` asked of `X`
through `AlgebraicGeometry.Space.HasEtaleLocalProperty`.

## References

* [Stacks Project, Tag 033I](https://stacks.math.columbia.edu/tag/033I)
* [Stacks Project, Tag 034F](https://stacks.math.columbia.edu/tag/034F)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0AD4](https://stacks.math.columbia.edu/tag/0AD4)
* [Stacks Project, Tag 0BGT](https://stacks.math.columbia.edu/tag/0BGT)
* [Stacks Project, Tag 0BH2](https://stacks.math.columbia.edu/tag/0BH2)
* [Stacks Project, Tag 0BH3](https://stacks.math.columbia.edu/tag/0BH3)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v w

namespace RingCat

/-- The compatible families of elements of a diagram of commutative rings form a commutative
ring. -/
instance commRing_sectionsSubring {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u}) :
    CommRing (sectionsSubring (F ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
  @Subring.toCommRing (∀ j, F.obj j) _
    (sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))

end RingCat

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Sections of the structure presheaf, read on one chart -/

section Charts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Evaluation of a global section of the structure presheaf of `X` on a single étale chart, as
a ring homomorphism. -/
private def evalChart (U : SmallEtale B S hS X) :
    RingCat.sectionsSubring (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})
      →+* Γ(chartScheme U, ⊤) where
  toFun s := s.val (Opposite.op U)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
private theorem evalChart_apply (U : SmallEtale B S hS X)
    (s : RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    evalChart U s = s.val (Opposite.op U) := rfl

/-- A global section of the structure presheaf of `X` is zero as soon as its value on every
étale chart is. -/
private theorem eq_zero_of_evalChart_eq_zero
    {s : RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (h : ∀ U : SmallEtale B S hS X, evalChart U s = 0) : s = 0 :=
  Subtype.ext (funext fun U => h U.unop)

/-- A point of a scheme lies in the non-vanishing locus of a global regular function exactly
when any of its preimages lies in the non-vanishing locus of the pulled back function. -/
private theorem mem_basicOpen_appTop_iff {A Y : Scheme.{u}} (f : A ⟶ Y) (r : Γ(Y, ⊤)) (a : A) :
    a ∈ A.basicOpen (f.appTop r) ↔ f a ∈ Y.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top]
  exact Scheme.Hom.mem_preimage f

end Charts

/-! ### Points of a chart, and the open loci they trace out in the space of points -/

section Points

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The set of points of a represented presheaf lying over an open subset of the representing
scheme is open for the point topology. -/
private theorem isOpen_preimage_pointsToScheme (U : BigFppfOver B S hS)
    {O : Set ((BigFppfOver.toScheme B S hS).obj U)} (hO : IsOpen O) :
    IsOpen (pointsToScheme B S hS U ⁻¹' O) :=
  (schemePointsHomeomorph B S hS U).isOpen_preimage.mpr hO

/-- The image in `|X|` of the points of an étale chart lying over an open subset of the chart's
scheme is open. -/
private theorem isOpen_image_pointsMap (U : SmallEtale B S hS X)
    {O : Set (chartScheme U)} (hO : IsOpen O) :
    IsOpen (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ''
      (pointsToScheme B S hS U.obj.left ⁻¹' O)) :=
  isOpenMap_pointsMap_of_presheafEtale B S hS U.obj.hom U.property _
    (isOpen_preimage_pointsToScheme U.obj.left hO)

/-- The image in `|X|` of the points of an étale chart lying over a nonempty subset of the
chart's scheme is nonempty. -/
private theorem nonempty_image_pointsMap (U : SmallEtale B S hS X)
    {O : Set (chartScheme U)} (hO : O.Nonempty) :
    (pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom ''
      (pointsToScheme B S hS U.obj.left ⁻¹' O)).Nonempty := by
  obtain ⟨y, hy⟩ := hO
  obtain ⟨p, hp⟩ := surjective_pointsToScheme B S hS U.obj.left y
  exact ⟨_, p, by rw [Set.mem_preimage, hp]; exact hy, rfl⟩

/-- If the space of points of `X` is irreducible, nonempty open subsets of two étale charts have
points with a common image in `|X|`. -/
private theorem exists_pointsMap_eq_of_nonempty [IrreducibleSpace (points B S hS X)]
    (U V : SmallEtale B S hS X) {O : Set (chartScheme U)} {O' : Set (chartScheme V)}
    (hO : IsOpen O) (hO' : IsOpen O') (hne : O.Nonempty) (hne' : O'.Nonempty) :
    ∃ (a : points B S hS (yoneda.obj U.obj.left)) (b : points B S hS (yoneda.obj V.obj.left)),
      pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom a =
        pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom b ∧
      pointsToScheme B S hS U.obj.left a ∈ O ∧ pointsToScheme B S hS V.obj.left b ∈ O' := by
  obtain ⟨z, hzV, hzU⟩ := ((isOpen_image_pointsMap U hO).dense
    (nonempty_image_pointsMap U hne)).inter_open_nonempty _ (isOpen_image_pointsMap V hO')
    (nonempty_image_pointsMap V hne')
  obtain ⟨a, ha, rfl⟩ := hzU
  obtain ⟨b, hb, hab⟩ := hzV
  exact ⟨a, b, hab.symm, ha, hb⟩

/-- Two points of two étale charts of `X` with the same image in `|X|` see the same global
section of the structure presheaf vanish or not vanish. -/
private theorem mem_basicOpen_iff_of_pointsMap_eq
    (s : RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (U V : SmallEtale B S hS X)
    (a : points B S hS (yoneda.obj U.obj.left)) (b : points B S hS (yoneda.obj V.obj.left))
    (hab : pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom a =
      pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom b) :
    pointsToScheme B S hS U.obj.left a ∈ (chartScheme U).basicOpen (evalChart U s) ↔
      pointsToScheme B S hS V.obj.left b ∈ (chartScheme V).basicOpen (evalChart V s) := by
  let W := U.property.rep.pullback V.obj.hom
  let p : W ⟶ U.obj.left := U.property.rep.fst' V.obj.hom
  let q : W ⟶ V.obj.left := U.property.rep.snd V.obj.hom
  have sq := U.property.rep.isPullback' V.obj.hom
  have hq : Etale ((BigFppfOver.toScheme B S hS).map q) := U.property.property_snd V.obj.hom
  let C : SmallEtale B S hS X :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ V.obj.hom),
      etale_comp_of_scheme B S hS q V.obj.hom hq V.property⟩
  let p' : C ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk p sq.w)
  let q' : C ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk q rfl)
  obtain ⟨c, hc, hc'⟩ := exists_points_of_isPullback B S hS sq a b hab
  have hp : (BigFppfOver.toScheme B S hS).map p (pointsToScheme B S hS W c) =
      pointsToScheme B S hS U.obj.left a := by
    rw [← pointsToScheme_pointsMap, hc]
  have hq' : (BigFppfOver.toScheme B S hS).map q (pointsToScheme B S hS W c) =
      pointsToScheme B S hS V.obj.left b := by
    rw [← pointsToScheme_pointsMap, hc']
  have hsp : ((BigFppfOver.toScheme B S hS).map p).appTop (evalChart U s) =
      evalChart C s := s.property p'.op
  have hsq : ((BigFppfOver.toScheme B S hS).map q).appTop (evalChart V s) =
      evalChart C s := s.property q'.op
  rw [← hp, ← hq', ← mem_basicOpen_appTop_iff, ← mem_basicOpen_appTop_iff, hsp, hsq]

end Points

/-! ### Every étale chart of an integral space is reduced -/

section EtaleLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale-local property of schemes which holds on some surjective étale atlas of an
algebraic space holds on every one of its étale charts. -/
private theorem property_chartScheme (P : ObjectProperty Scheme.{u})
    [P.IsLocal Scheme.etalePrecoverage] (hX : IsAlgebraicSpace B S hS X)
    (hP : HasEtaleLocalProperty B S hS X P) (U : SmallEtale B S hS X) :
    P (chartScheme U) :=
  (exists_atlas_iff_forall_etale B S hS X P hX).mp hP U.obj.left U.obj.hom U.property

/-- Every étale chart of a reduced algebraic space is reduced. -/
private theorem isReduced_chartScheme (hX : IsAlgebraicSpace B S hS X)
    (hred : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsReduced Y))
    (U : SmallEtale B S hS X) : IsReduced (chartScheme U) :=
  property_chartScheme _ hX hred U

/-- Every étale chart of a normal algebraic space is normal. -/
private theorem isNormal_chartScheme (hX : IsAlgebraicSpace B S hS X)
    (hnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsNormal Y))
    (U : SmallEtale B S hS X) : IsNormal (chartScheme U) :=
  property_chartScheme _ hX hnormal U

end EtaleLocal

/-! ### A nonzero global section vanishes nowhere -/

section NonVanishing

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If the space of points of `X` is irreducible and every étale chart of `X` is reduced, then a
nonzero global regular function on `X` has nonzero germ at every point of every chart. -/
private theorem germ_ne_zero_of_ne_zero
    (hirr : IrreducibleSpace (points B S hS X))
    (hred : ∀ U : SmallEtale B S hS X, IsReduced (chartScheme U))
    {s : RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hs : s ≠ 0) (U : SmallEtale B S hS X) (x : chartScheme U) :
    ((chartScheme U).presheaf.germ ⊤ x trivial).hom (evalChart U s) ≠ 0 := by
  classical
  obtain ⟨V, hV⟩ := not_forall.mp (mt eq_zero_of_evalChart_eq_zero hs)
  have := hred U
  have := hred V
  have hn : (((chartScheme V).basicOpen (evalChart V s) :
      (chartScheme V).Opens) : Set (chartScheme V)).Nonempty :=
    nonempty_basicOpen_of_ne_zero _ hV
  intro hz
  obtain ⟨W, hxW, i, j, hij⟩ := (chartScheme U).presheaf.germ_eq x
    (show x ∈ (⊤ : (chartScheme U).Opens) from trivial)
    (show x ∈ (⊤ : (chartScheme U).Opens) from trivial)
    (evalChart U s) 0 (by simpa using hz)
  have hw : (chartScheme U).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (evalChart U s) = 0 := by
    rwa [show i = homOfLE (le_top : W ≤ ⊤) from Subsingleton.elim _ _, map_zero] at hij
  have hbot : W ⊓ (chartScheme U).basicOpen (evalChart U s) = ⊥ := by
    rw [← Scheme.basicOpen_res _ (evalChart U s) (homOfLE (le_top : W ≤ ⊤)).op, hw,
      Scheme.basicOpen_zero]
  obtain ⟨a, b, hab, ha, hb⟩ := exists_pointsMap_eq_of_nonempty (X := X) U V
    (W : (chartScheme U).Opens).isOpen ((chartScheme V).basicOpen (evalChart V s)).isOpen
    ⟨x, hxW⟩ hn
  have hmem : pointsToScheme B S hS U.obj.left a ∈
      W ⊓ (chartScheme U).basicOpen (evalChart U s) :=
    ⟨ha, (mem_basicOpen_iff_of_pointsMap_eq s U V a b hab).mpr hb⟩
  rw [hbot] at hmem
  exact hmem

end NonVanishing

/-! ### Stacks 0BH2 -/

/-- The ring of global regular functions on an integral algebraic space, the compatible families
of regular functions on its étale charts, is a domain. -/
@[stacks 0BH2]
theorem isDomain_globalSections_of_isIntegralSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hXint : IsIntegralSpace B S hS X) :
    IsDomain (RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) := by
  classical
  have : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace B S hS X
  have hred : ∀ U : SmallEtale B S hS X, IsReduced (chartScheme U) :=
    isReduced_chartScheme hX (hXint.hasEtaleLocalProperty_isReduced B S hS X)
  obtain ⟨U₀, f₀, hsurj, hetale, -⟩ := hXint.hasEtaleLocalProperty_isReduced B S hS X
  let V : SmallEtale B S hS X := ⟨CostructuredArrow.mk f₀, hetale⟩
  obtain ⟨p, -⟩ := isSurjective_of_presheafSurjective B S hS f₀ hsurj
    (Classical.choice (inferInstance : Nonempty (points B S hS X)))
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).2 ⟨⟨fun {g h} hgh => ?_⟩, ⟨⟨1, 0, ?_⟩⟩⟩
  · refine or_iff_not_and_not.2 fun ⟨hg, hh⟩ => ?_
    obtain ⟨U, hU⟩ := not_forall.mp (mt eq_zero_of_evalChart_eq_zero hg)
    obtain ⟨U', hU'⟩ := not_forall.mp (mt eq_zero_of_evalChart_eq_zero hh)
    have := hred U
    have := hred U'
    obtain ⟨a, b, hab, ha, hb⟩ := exists_pointsMap_eq_of_nonempty (X := X) U U'
      ((chartScheme U).basicOpen (evalChart U g)).isOpen
      ((chartScheme U').basicOpen (evalChart U' h)).isOpen
      (nonempty_basicOpen_of_ne_zero _ hU) (nonempty_basicOpen_of_ne_zero _ hU')
    have hmem : pointsToScheme B S hS U.obj.left a ∈
        (chartScheme U).basicOpen (evalChart U (g * h)) := by
      rw [map_mul, Scheme.basicOpen_mul]
      exact ⟨ha, (mem_basicOpen_iff_of_pointsMap_eq h U U' a b hab).mpr hb⟩
    rw [hgh, map_zero, Scheme.basicOpen_zero] at hmem
    exact hmem
  · intro h10
    have hx : pointsToScheme B S hS U₀ p ∈
        (chartScheme V).basicOpen (evalChart V (1 : RingCat.sectionsSubring
          (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u}))) := by
      simp
    rw [h10, map_zero, Scheme.basicOpen_zero] at hx
    exact hx

/-! ### Gluing a stalkwise quotient -/

section Gluing

/-- A stalkwise solution of `b ⬝ c = a` with `b` a nonzerodivisor in every stalk glues to a
global solution. -/
private theorem exists_mul_eq_of_forall_stalk (T : TopCat.{u}) (F : T.Sheaf CommRingCat.{u})
    (a b : F.presheaf.obj (Opposite.op ⊤))
    (hb : ∀ y : T, Function.Injective
      (fun c : F.presheaf.stalk y => (F.presheaf.germ ⊤ y trivial).hom b * c))
    (hlocal : ∀ y : T, ∃ c : F.presheaf.stalk y,
      (F.presheaf.germ ⊤ y trivial).hom b * c = (F.presheaf.germ ⊤ y trivial).hom a) :
    ∃ c : F.presheaf.obj (Opposite.op ⊤), b * c = a := by
  classical
  choose c hc using hlocal
  choose U hxU s hs using fun y => F.presheaf.exists_germ_eq (c y)
  choose V hxV i₁ i₂ hEq using fun y =>
    F.presheaf.germ_eq y (hxU y) (hxU y)
      ((F.presheaf.map (homOfLE (le_top : U y ≤ ⊤)).op) b * s y)
      ((F.presheaf.map (homOfLE (le_top : U y ≤ ⊤)).op) a) (by
        rw [map_mul, F.presheaf.germ_res_apply, F.presheaf.germ_res_apply, hs y]
        exact hc y)
  let localSec (y : T) : F.presheaf.obj (Opposite.op (V y)) := F.presheaf.map (i₂ y).op (s y)
  have hlocalEq (y : T) :
      (F.presheaf.map (homOfLE (le_top : V y ≤ ⊤)).op) b * localSec y =
        (F.presheaf.map (homOfLE (le_top : V y ≤ ⊤)).op) a := by
    have h := hEq y
    rw [show i₁ y = i₂ y from Subsingleton.elim _ _] at h
    simp only [map_mul, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at h
    rw [show (i₂ y ≫ homOfLE (le_top : U y ≤ ⊤)).op = (homOfLE (le_top : V y ≤ ⊤)).op from
      Subsingleton.elim _ _] at h
    exact h
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V localSec := by
    intro y y'
    apply TopCat.Presheaf.section_ext F (V y ⊓ V y')
    intro x hx
    have hgerm (k : T) (hk : x ∈ V k) :
        (F.presheaf.germ ⊤ x trivial).hom b *
            (F.presheaf.germ (V k) x hk).hom (localSec k) =
          (F.presheaf.germ ⊤ x trivial).hom a := by
      simpa using congrArg (F.presheaf.germ (V k) x hk).hom (hlocalEq k)
    apply hb x
    simpa only [F.presheaf.germ_res_apply] using (hgerm y hx.1).trans (hgerm y' hx.2).symm
  obtain ⟨t, ht, -⟩ :=
    F.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top)
      (fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩) localSec hcompat
  let tΓ : F.presheaf.obj (Opposite.op ⊤) := t
  refine ⟨tΓ, ?_⟩
  apply TopCat.Presheaf.section_ext F ⊤
  intro x _
  have ht' : (F.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op) tΓ = localSec x := by
    convert ht x using 1
  have h := congrArg (F.presheaf.germ (V x) x (hxV x)).hom (hlocalEq x)
  rw [← ht'] at h
  change (F.presheaf.germ ⊤ x trivial).hom (b * tΓ) = (F.presheaf.germ ⊤ x trivial).hom a
  simpa only [map_mul, F.presheaf.germ_res_apply] using h

/-- If an element of the fraction field of a domain `R` is integral over `R` and equals `a / b`,
then `b ⬝ c = a` has a solution in every integrally closed domain `A` receiving `R`
injectively. -/
private theorem exists_mul_eq_of_isIntegral {R A : Type*} [CommRing R] [IsDomain R]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (f : R →+* A) (hf : Function.Injective f)
    (z : FractionRing R) (hz : _root_.IsIntegral R z) (a b : R)
    (hab : algebraMap R (FractionRing R) b * z = algebraMap R (FractionRing R) a) :
    ∃ c : A, f b * c = f a := by
  have hg : Function.Injective ((algebraMap A (FractionRing A)).comp f) :=
    (IsFractionRing.injective A (FractionRing A)).comp hf
  have hφ (r : R) : IsFractionRing.lift hg (algebraMap R (FractionRing R) r) =
      algebraMap A (FractionRing A) (f r) := IsFractionRing.lift_algebraMap hg r
  have hzA : _root_.IsIntegral A (IsFractionRing.lift hg z) := by
    have hcomp : (IsFractionRing.lift hg).comp (algebraMap R (FractionRing R)) =
        (algebraMap A (FractionRing A)).comp f := RingHom.ext hφ
    have H := RingHom.IsIntegralElem.map hz (IsFractionRing.lift hg)
    rw [hcomp] at H
    exact H.of_comp
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp ‹_› hzA
  refine ⟨c, (IsFractionRing.injective A (FractionRing A)) ?_⟩
  rw [map_mul, hc, ← hφ b, ← hφ a, ← map_mul, hab]

end Gluing

/-! ### Stacks 0BH3 -/

/-- The ring of global regular functions on a normal integral algebraic space, the compatible
families of regular functions on its étale charts, is a normal domain. -/
@[stacks 0BH3, ega "II 8.8.6.1"]
theorem isNormalDomain_globalSections_of_isIntegralSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hXint : IsIntegralSpace B S hS X)
    (hXnormal : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsNormal Y)) :
    IsNormalDomain (RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) := by
  classical
  set R := RingCat.sectionsSubring
    (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})
  have : IsDomain R := isDomain_globalSections_of_isIntegralSpace B S hS X hX hXint
  have hred : ∀ U : SmallEtale B S hS X, IsReduced (chartScheme U) :=
    isReduced_chartScheme hX (hXint.hasEtaleLocalProperty_isReduced B S hS X)
  have hirr : IrreducibleSpace (points B S hS X) := hXint.irreducibleSpace B S hS X
  have hnormal : ∀ U : SmallEtale B S hS X, IsNormal (chartScheme U) :=
    isNormal_chartScheme hX hXnormal
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro z hz
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap R (FractionRing R) b ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (R := R) (K := FractionRing R)).not.mpr hb0
  have hba : algebraMap R (FractionRing R) b * z = algebraMap R (FractionRing R) a := by
    rw [← hab]
    field_simp
  have hbnz (U : SmallEtale B S hS X) (x : chartScheme U) :
      ((chartScheme U).presheaf.germ ⊤ x trivial).hom (evalChart U b) ≠ 0 :=
    germ_ne_zero_of_ne_zero hirr hred hb0 U x
  have hex (U : SmallEtale B S hS X) :
      ∃ c : Γ(chartScheme U, ⊤), evalChart U b * c = evalChart U a := by
    have := hnormal U
    have hcancel : ∀ x : chartScheme U, Function.Injective
        (fun d : (chartScheme U).presheaf.stalk x =>
          ((chartScheme U).presheaf.germ ⊤ x trivial).hom (evalChart U b) * d) :=
      fun x _ _ hcd => mul_left_cancel₀ (hbnz U x) hcd
    refine exists_mul_eq_of_forall_stalk (chartScheme U) (chartScheme U).sheaf
      (evalChart U a) (evalChart U b) hcancel (fun x => ?_)
    have : IsIntegrallyClosed ((chartScheme U).presheaf.stalk x) := IsNormal.stalk_normal x
    refine exists_mul_eq_of_isIntegral
      (((chartScheme U).presheaf.germ ⊤ x trivial).hom.comp (evalChart U)) ?_ z hz a b hba
    exact (injective_iff_map_eq_zero _).mpr fun r hr =>
      not_not.1 fun hr0 => germ_ne_zero_of_ne_zero hirr hred hr0 U x hr
  choose c hc using hex
  have hinj (U : SmallEtale B S hS X) :
      Function.Injective (fun t : Γ(chartScheme U, ⊤) => evalChart U b * t) := by
    have := hnormal U
    intro t t' ht
    have hgerm : ∀ (x : chartScheme U) (hx : x ∈ (⊤ : (chartScheme U).Opens)),
        ((chartScheme U).presheaf.germ ⊤ x hx).hom t =
          ((chartScheme U).presheaf.germ ⊤ x hx).hom t' := fun x hx =>
      mul_left_cancel₀ (hbnz U x) (by
        simpa only [map_mul] using congrArg ((chartScheme U).presheaf.germ ⊤ x hx).hom ht)
    exact TopCat.Presheaf.section_ext (chartScheme U).sheaf ⊤ t t' hgerm
  obtain ⟨t, hbt⟩ : ∃ t : R, b * t = a := by
    refine ⟨⟨fun U => c U.unop, fun {U V} f => ?_⟩, ?_⟩
    · let m : Γ(chartScheme U.unop, ⊤) →+* Γ(chartScheme V.unop, ⊤) :=
        ((structurePresheaf B S hS X).map f).hom
      have hbm : m (evalChart U.unop b) = evalChart V.unop b := b.property f
      have ham : m (evalChart U.unop a) = evalChart V.unop a := a.property f
      have h : evalChart V.unop b * m (c U.unop) = evalChart V.unop a := by
        rw [← hbm, ← ham, ← map_mul, hc U.unop]
      exact hinj V.unop (h.trans (hc V.unop).symm)
    · exact Subtype.ext (funext fun U => hc U.unop)
  exact ⟨t, mul_left_cancel₀ hbK (by rw [← map_mul, hbt, hba])⟩

end AlgebraicGeometry.Space

end
