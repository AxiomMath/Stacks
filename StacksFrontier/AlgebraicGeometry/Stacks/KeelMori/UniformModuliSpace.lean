module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliMapProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Keel–Mori moduli map is a uniform categorical moduli space (Stacks 0DUT)

Let `f : 𝒳 ⟶ M` be a 1-morphism from a category fibred in groupoids to an algebraic space, and let
`mᵢ : Mᵢ ⟶ M` be a family of flat morphisms of algebraic spaces along which every point of `M`
lifts locally, such that every square
```
𝒳ᵢ ⟶ 𝒳
 ↓      ↓ f
Mᵢ ⟶ M
```
is 2-cartesian with `𝒳ᵢ ⟶ Mᵢ` a uniform categorical moduli space. Then `f` is a uniform
categorical moduli space.

## Main definitions

* `AlgebraicGeometry.Stack.LiftsSectionsLocally`: a family of morphisms of presheaves along which
  every section of the target lifts locally.

## Main results

* `AlgebraicGeometry.Stack.glueSections`, `AlgebraicGeometry.Stack.comp_glueSections`,
  `AlgebraicGeometry.Stack.hom_ext_of_liftsSectionsLocally`: gluing morphisms into a sheaf along
  such a family.
* `AlgebraicGeometry.Stack.isUniformCategoricalModuliSpace_of_pieces`: a 1-morphism which is,
  along such a family of flat morphisms, the base change of uniform categorical moduli spaces is
  a uniform categorical moduli space.
* `AlgebraicGeometry.Stack.KeelMoriCover.isUniformCategoricalModuliSpace_moduliMap`: the moduli
  map of a small Keel–Mori cover is a uniform categorical moduli space (Stacks 0DUT).

## References

* [Stacks Project, Tag 0DUT](https://stacks.math.columbia.edu/tag/0DUT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w v v₁ u₁

/-! ### Gluing morphisms into a sheaf along a family which lifts sections locally -/

section PresheafGlue

variable {C : Type u₁} [Category.{v} C] {Y E : Cᵒᵖ ⥤ Type v} {ι : Type*}
  {Yi : ι → Cᵒᵖ ⥤ Type v} (b : ∀ i, Yi i ⟶ Y)

/-- The sieve of the arrows along which a section of `Y` is the image of a section of some member
of the family `b`. -/
def liftSieve {T : C} (y : Y.obj (op T)) : Sieve T where
  arrows V k := ∃ (i : ι) (z : (Yi i).obj (op V)), (b i).app (op V) z = Y.map k.op y
  downward_closed := by
    rintro V W k ⟨i, z, hz⟩ g
    refine ⟨i, (Yi i).map g.op z, ?_⟩
    rw [NatTrans.naturality_apply, hz, ← Functor.map_comp_apply, ← op_comp]

/-- A family of morphisms of presheaves `b i : Yi i ⟶ Y` **lifts sections locally** for `J` when
every section of `Y` is, along the arrows of a covering sieve, the image of a section of some
`Yi i`. -/
@[sga "3 IV 4.4.8"]
def LiftsSectionsLocally (J : GrothendieckTopology C) : Prop :=
  ∀ (T : C) (y : Y.obj (op T)), liftSieve b y ∈ J T

variable {b} {J : GrothendieckTopology C}

/-- **A family along which sections lift locally may be tested on any covering sieve.** -/
theorem liftsSectionsLocally_of_exists
    (h : ∀ (T : C) (y : Y.obj (op T)), ∃ R ∈ J T, ∀ ⦃V : C⦄ ⦃k : V ⟶ T⦄, R.arrows k →
      ∃ (i : ι) (z : (Yi i).obj (op V)), (b i).app (op V) z = Y.map k.op y) :
    LiftsSectionsLocally b J := fun T y =>
  let ⟨_, hR, hl⟩ := h T y
  J.superset_covering (fun _ _ hk => hl hk) hR

variable (ψ : ∀ i, Yi i ⟶ E)
  (hψ : ∀ (i j : ι) (V : C) (zi : (Yi i).obj (op V)) (zj : (Yi j).obj (op V)),
    (b i).app (op V) zi = (b j).app (op V) zj → (ψ i).app (op V) zi = (ψ j).app (op V) zj)

/-- The family of elements of `E` on `liftSieve b y` given by the `ψ i`. -/
noncomputable def localFamily {T : C} (y : Y.obj (op T)) :
    Presieve.FamilyOfElements E (liftSieve b y).arrows :=
  fun _ _ hk => (ψ hk.choose).app _ hk.choose_spec.choose

include hψ in
/-- The local family takes the value `ψ i z` at any lift `z` of the restricted section. -/
theorem localFamily_eq {T V : C} {y : Y.obj (op T)} {k : V ⟶ T} (hk : (liftSieve b y).arrows k)
    (i : ι) (z : (Yi i).obj (op V)) (hz : (b i).app (op V) z = Y.map k.op y) :
    localFamily (b := b) ψ y k hk = (ψ i).app (op V) z :=
  hψ _ _ _ _ _ (hk.choose_spec.choose_spec.trans hz.symm)

include hψ in
/-- The local family is compatible. -/
theorem localFamily_compatible {T : C} (y : Y.obj (op T)) :
    (localFamily (b := b) ψ y).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  change E.map g₁.op ((ψ _).app _ _) = E.map g₂.op ((ψ _).app _ _)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  apply hψ
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h₁.choose_spec.choose_spec,
    h₂.choose_spec.choose_spec, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, hcomm]

variable (hb : LiftsSectionsLocally b J) (hE : Presieve.IsSheaf J E)

/-- The glued section at a section of `Y`. -/
noncomputable def glueSectionsAt {T : C} (y : Y.obj (op T)) : E.obj (op T) :=
  (hE _ (hb T y)).amalgamate (localFamily (b := b) ψ y) (localFamily_compatible (b := b) ψ hψ y)

/-- The glued section restricts to the local family along the arrows of `liftSieve b y`. -/
theorem map_glueSectionsAt {T V : C} (y : Y.obj (op T)) {k : V ⟶ T}
    (hk : (liftSieve b y).arrows k) :
    E.map k.op (glueSectionsAt ψ hψ hb hE y) = localFamily (b := b) ψ y k hk :=
  (hE _ (hb T y)).valid_glue _ _ hk

/-- **The glued morphism of presheaves** `Y ⟶ E`. -/
noncomputable def glueSections : Y ⟶ E where
  app T := TypeCat.ofHom fun y => glueSectionsAt ψ hψ hb hE (T := T.unop) y
  naturality T T' h := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    change glueSectionsAt ψ hψ hb hE (Y.map h y) = E.map h (glueSectionsAt ψ hψ hb hE y)
    refine (hE _ (hb T'.unop (Y.map h y))).isSeparatedFor.ext fun V k hk => ?_
    obtain ⟨i, z, hz⟩ := hk
    have hk' : (liftSieve b y).arrows (k ≫ h.unop) :=
      ⟨i, z, by rw [hz, op_comp, Functor.map_comp_apply]; rfl⟩
    refine (map_glueSectionsAt ψ hψ hb hE _ ⟨i, z, hz⟩).trans
      ((localFamily_eq ψ hψ ⟨i, z, hz⟩ i z hz).trans ?_)
    rw [← Functor.map_comp_apply, show h ≫ k.op = (k ≫ h.unop).op from rfl,
      map_glueSectionsAt ψ hψ hb hE _ hk']
    exact (localFamily_eq ψ hψ hk' i z
      (by rw [hz, op_comp, Functor.map_comp_apply]; rfl)).symm

/-- The glued morphism restricts to `ψ i` along `b i`. -/
theorem comp_glueSections (i : ι) : b i ≫ glueSections ψ hψ hb hE = ψ i := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun z => ?_)
  change glueSectionsAt ψ hψ hb hE ((b i).app T z) = (ψ i).app T z
  refine (hE _ (hb T.unop ((b i).app T z))).isSeparatedFor.ext fun V k hk => ?_
  refine (map_glueSectionsAt ψ hψ hb hE _ hk).trans ?_
  refine (localFamily_eq ψ hψ hk i ((Yi i).map k.op z) (NatTrans.naturality_apply _ _ _)).trans ?_
  exact NatTrans.naturality_apply _ _ _

include hb hE in
/-- **Two morphisms into a sheaf agreeing along a family which lifts sections locally are
equal.** -/
theorem hom_ext_of_liftsSectionsLocally {φ₁ φ₂ : Y ⟶ E} (h : ∀ i, b i ≫ φ₁ = b i ≫ φ₂) :
    φ₁ = φ₂ := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun y => ?_)
  refine (hE _ (hb T.unop y)).isSeparatedFor.ext fun V k hk => ?_
  obtain ⟨i, z, hz⟩ := hk
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← hz]
  exact congrFun (congrArg (fun φ => φ.app (op V)) (h i)) z

end PresheafGlue

section PullbackLift

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C} {Y M : Cᵒᵖ ⥤ Type v}
  {ι : Type*} {Mi : ι → Cᵒᵖ ⥤ Type v} {m : ∀ i, Mi i ⟶ M}

/-- Sections of the two factors with the same image in the base come from a section of the
pullback presheaf. -/
private theorem exists_pullback_section {Z : Cᵒᵖ ⥤ Type v} {a : Y ⟶ M} {n : Z ⟶ M} {V : C}
    (y : Y.obj (op V)) (z : Z.obj (op V)) (h : a.app (op V) y = n.app (op V) z) :
    ∃ w : (pullback a n).obj (op V),
      (pullback.fst a n).app (op V) w = y ∧ (pullback.snd a n).app (op V) w = z := by
  refine ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm y) (yonedaEquiv.symm z)
    (yonedaEquiv.injective (by simpa [yonedaEquiv_comp] using h))), ?_, ?_⟩ <;>
    rw [← yonedaEquiv_comp]
  · rw [pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [pullback.lift_snd, Equiv.apply_symm_apply]

/-- **Local lifting of sections is stable under base change.** -/
theorem liftsSectionsLocally_pullback_fst (hm : LiftsSectionsLocally m J) (a : Y ⟶ M) :
    LiftsSectionsLocally (fun i => pullback.fst a (m i)) J := fun T y => by
  refine J.superset_covering ?_ (hm T (a.app _ y))
  rintro V k ⟨i, n, hn⟩
  exact (exists_pullback_section (a := a) (Y.map k.op y) n
    ((NatTrans.naturality_apply a k.op y).trans hn.symm)).elim fun w hw => ⟨i, w, hw.1⟩

end PullbackLift

/-! ### Uniform categorical moduli spaces from pieces -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The second projections of the canonical 2-fibre products along a family which lifts
sections locally lift objects locally.** -/
theorem liftsLocally_twoFibreProductSquare_snd
    {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (F : 𝒴 ⟶ fibredCategory B S hS Y) {ι : Type*}
    {Yi : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {b : ∀ i, Yi i ⟶ Y}
    (hb : LiftsSectionsLocally b (BigFppfOver.topology B S hS)) :
    LiftsLocally (fun i => (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS (b i)).1 F).snd) := by
  intro x
  have hb₀ : (F.hom.obj x).base = 𝒴.val.p.obj x := Functor.congr_obj F.hom.w x
  refine ⟨liftSieve b (PresheafOfCategories.elementOf Y hb₀), hb _ _, fun V k hk => ?_⟩
  obtain ⟨i, z, hz⟩ := hk
  obtain ⟨x₁, a₁, ha₁⟩ := exists_lift_obj (𝒜 := 𝒴) x k
  have hx₁ : 𝒴.val.p.obj x₁ = V := IsHomLift.domain_eq _ k a₁
  have hFx₁ : (F.hom.obj x₁).base = V := (Functor.congr_obj F.hom.w x₁).trans hx₁
  have hFa₁ : (fibredCategory B S hS Y).val.p.IsHomLift k (F.hom.map a₁) :=
    Functor.isHomLift_map_of_comp_eq F.hom.w k a₁
  let zV : (fibredCategory B S hS (Yi i)).val.obj := ⟨V, Discrete.mk z⟩
  have hbz : ((associatedMap B S hS (b i)).1.hom.obj zV).base = V := by
    rw [associatedMap_obj]
  have e₁ : (associatedMap B S hS (b i)).1.hom.obj zV = F.hom.obj x₁ := by
    rw [associatedMap_obj]
    refine PresheafOfCategories.obj_eq_of_elementOf_eq (P := Y) rfl hFx₁ ?_
    rw [ChartBaseChange.fibredCategory_elementOf_eq_map hFx₁ hb₀ k (F.hom.map a₁) hFa₁, ← hz]
    rfl
  let w : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS (b i)).1 F).pt.val.obj :=
    { base := V, x := zV, y := x₁, hx := rfl, hy := hx₁, iso := eqToIso e₁
      vertical := IsHomLift.eqToHom_domain_lift_id e₁ hbz }
  exact ⟨i, w, a₁, ha₁⟩

section Pieces

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {M : AlgebraicSpaces B S hS} (f : 𝒳 ⟶ fibredCategory B S hS M.obj)
  {ι : Type*} {Mi : ι → AlgebraicSpaces B S hS} (m : ∀ i, Mi i ⟶ M)
  (Q : ∀ i, Bicategory.TwoCommSq (associatedMap B S hS (m i).hom).1 f)
  (hQ : ∀ i, Bicategory.IsTwoFibreProduct (Q i))
  (hQu : ∀ i, IsUniformCategoricalModuliSpace B S hS (Mi i) (Q i).fst)

include hQ hQu in
/-- **A 2-fibre product of `f` along a morphism factoring flatly through a piece is a categorical
moduli space.** -/
theorem isCategoricalModuliSpace_fst_of_comp_piece (i : ι) {Z : AlgebraicSpaces B S hS}
    (c : Z ⟶ Mi i) (hc : Space.IsFlat B S hS c.hom)
    {z : fibredCategory B S hS Z.obj ⟶ fibredCategory B S hS M.obj}
    (hz : z = (associatedMap B S hS c.hom).1 ≫ (associatedMap B S hS (m i).hom).1)
    (R : Bicategory.TwoCommSq z f) (hR : Bicategory.IsTwoFibreProduct R) :
    IsCategoricalModuliSpace B S hS Z R.fst := by
  subst hz
  let T := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS c.hom).1 (Q i).fst
  have hT := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (associatedMap B S hS c.hom).1 (Q i).fst
  exact isCategoricalModuliSpace_of_isTwoFibreProduct B S hS hR
    (Bicategory.isTwoFibreProduct_pasteFst (Q i) (hQ i) T hT) (hQu i Z c hc T hT)

include hQ hQu in
/-- **A 1-morphism to an algebraic space which is, along a family of flat morphisms
`mᵢ : Mᵢ ⟶ M` lifting the points of `M` locally, the base change of uniform categorical moduli
spaces `𝒳ᵢ ⟶ Mᵢ`, is a uniform categorical moduli space.** -/
theorem isUniformCategoricalModuliSpace_of_pieces (hm : ∀ i, Space.IsFlat B S hS (m i).hom)
    (hlift : LiftsSectionsLocally (fun i => (m i).hom) (BigFppfOver.topology B S hS)) :
    IsUniformCategoricalModuliSpace B S hS M f := by
  intro Y' a ha P hP W θ
  classical
  have hE : Presieve.IsSheaf (BigFppfOver.topology B S hS) W.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 W.property.isSheaf
  let Yi : ι → AlgebraicSpaces B S hS := fun i =>
    ⟨pullback a.hom (m i).hom,
      isAlgebraicSpace_pullback B S hS _ _ Y'.property (Mi i).property M.property⟩
  let b : ∀ i, Yi i ⟶ Y' := fun i => ObjectProperty.homMk (pullback.fst a.hom (m i).hom)
  let c : ∀ i, Yi i ⟶ Mi i := fun i => ObjectProperty.homMk (pullback.snd a.hom (m i).hom)
  have hbc : ∀ i, (b i).hom ≫ a.hom = (c i).hom ≫ (m i).hom := fun i => pullback.condition
  have hbflat : ∀ i, Space.IsFlat B S hS (b i).hom := fun i =>
    Space.isFlat_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback _ _)
      (Mi i).property M.property (hm i)
  have hcflat : ∀ i, Space.IsFlat B S hS (c i).hom := fun i =>
    Space.isFlat_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback _ _).flip
      Y'.property M.property ha
  have hbl : LiftsSectionsLocally (fun i => (b i).hom) (BigFppfOver.topology B S hS) :=
    liftsSectionsLocally_pullback_fst hlift a.hom
  let D : ∀ i, Bicategory.TwoCommSq (associatedMap B S hS (b i).hom).1 P.fst := fun i =>
    CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hD : ∀ i, Bicategory.IsTwoFibreProduct (D i) := fun i =>
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have eD : ∀ i, (D i).fst ≫ (associatedMap B S hS (b i).hom).1 = (D i).snd ≫ P.fst := fun i =>
    hom_eq_of_hom₂ B S hS (D i).iso.hom
  have hDc : ∀ i, IsCategoricalModuliSpace B S hS (Yi i) (D i).fst := fun i =>
    isCategoricalModuliSpace_fst_of_comp_piece f m Q hQ hQu i (c i) (hcflat i)
      (by rw [← associatedMap_comp, ← associatedMap_comp, hbc]) _
      (Bicategory.isTwoFibreProduct_pasteFst P hP (D i) (hD i))
  have hψex : ∀ i, ∃ ψ : Yi i ⟶ W,
      (D i).fst ≫ (associatedMap B S hS ψ.hom).1 = (D i).snd ≫ θ := fun i => by
    obtain ⟨ψ, ⟨η⟩, -⟩ := hDc i W ((D i).snd ≫ θ)
    exact ⟨ψ, hom_eq_of_hom₂ B S hS η.hom⟩
  choose ψ hψ using hψex
  have hpair : ∀ i j, pullback.fst (b i).hom (b j).hom ≫ (ψ i).hom =
      pullback.snd (b i).hom (b j).hom ≫ (ψ j).hom := by
    intro i j
    let Yij : AlgebraicSpaces B S hS := ⟨pullback (b i).hom (b j).hom,
      isAlgebraicSpace_pullback B S hS _ _ (Yi i).property (Yi j).property Y'.property⟩
    let p₁ : Yij ⟶ Yi i := ObjectProperty.homMk (pullback.fst _ _)
    let p₂ : Yij ⟶ Yi j := ObjectProperty.homMk (pullback.snd _ _)
    have hp₁ : Space.IsFlat B S hS p₁.hom :=
      Space.isFlat_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback _ _)
        (Yi j).property Y'.property (hbflat j)
    let Dij := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS p₁.hom).1 (D i).fst
    have hDij := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (associatedMap B S hS p₁.hom).1 (D i).fst
    have hcat : IsCategoricalModuliSpace B S hS Yij Dij.fst :=
      isCategoricalModuliSpace_fst_of_comp_piece f m Q hQ hQu i (p₁ ≫ c i)
        (Space.isFlat_comp B S hS Yij.property (Yi i).property (Mi i).property _ _ hp₁
          (hcflat i))
        (by
          change _ = (associatedMap B S hS (p₁.hom ≫ (c i).hom)).1 ≫ _
          rw [← associatedMap_comp, ← associatedMap_comp, ← associatedMap_comp, Category.assoc,
            hbc, Category.assoc]) _
        (Bicategory.isTwoFibreProduct_pasteFst P hP _
          (Bicategory.isTwoFibreProduct_pasteFst (D i) (hD i) Dij hDij))
    have e₁ : Dij.fst ≫ (associatedMap B S hS p₁.hom).1 = Dij.snd ≫ (D i).fst :=
      hom_eq_of_hom₂ B S hS Dij.iso.hom
    have hsq : (Dij.fst ≫ (associatedMap B S hS p₂.hom).1) ≫ (associatedMap B S hS (b j).hom).1 =
        (Dij.snd ≫ (D i).snd) ≫ P.fst := by
      rw [discrete_assoc, ← associatedMap_comp,
        show p₂.hom ≫ (b j).hom = p₁.hom ≫ (b i).hom from pullback.condition.symm,
        associatedMap_comp, ← discrete_assoc, e₁, discrete_assoc, eD i, discrete_assoc]
    let w := Bicategory.twoFibreProductPreHom (hD j)
      ⟨Dij.pt, Dij.fst ≫ (associatedMap B S hS p₂.hom).1, Dij.snd ≫ (D i).snd, eqToIso hsq⟩
    have w₁ : Dij.fst ≫ (associatedMap B S hS p₂.hom).1 = w.hom ≫ (D j).fst :=
      hom_eq_of_hom₂ B S hS w.isoFst.hom
    have w₂ : (Dij.snd ≫ (D i).snd) ≫ θ = (w.hom ≫ (D j).snd) ≫ θ :=
      discrete_whisker w.isoSnd.hom θ
    have key := eq_of_isCategoricalModuliSpace B S hS hcat ((Dij.snd ≫ (D i).snd) ≫ θ)
      (p₁ ≫ ψ i) (p₂ ≫ ψ j) ⟨eqToIso (by
        change Dij.fst ≫ (associatedMap B S hS (p₁.hom ≫ (ψ i).hom)).1 = _
        rw [associatedMap_comp, ← discrete_assoc, e₁, discrete_assoc, hψ i, discrete_assoc])⟩
      ⟨eqToIso (by
        change Dij.fst ≫ (associatedMap B S hS (p₂.hom ≫ (ψ j).hom)).1 = _
        rw [associatedMap_comp, ← discrete_assoc, w₁, discrete_assoc, hψ j]
        exact (discrete_assoc _ _ _).symm.trans w₂.symm)⟩
    exact congrArg (·.hom) key
  have hcompat : ∀ (i j : ι) (V : BigFppfOver B S hS) (zi : (Yi i).obj.obj (op V))
      (zj : (Yi j).obj.obj (op V)), (b i).hom.app (op V) zi = (b j).hom.app (op V) zj →
        (ψ i).hom.app (op V) zi = (ψ j).hom.app (op V) zj := by
    intro i j V zi zj h
    obtain ⟨w, hw₁, hw₂⟩ := exists_pullback_section zi zj h
    simpa [hw₁, hw₂] using congrArg (fun φ => φ.app (op V) w) (hpair i j)
  let ψg : Y'.obj ⟶ W.obj := glueSections (fun i => (ψ i).hom) hcompat hbl hE
  have hglue : ∀ i, (b i).hom ≫ ψg = (ψ i).hom := comp_glueSections _ hcompat hbl hE
  refine ⟨ObjectProperty.homMk ψg, ⟨eqToIso ?_⟩, ?_⟩
  · refine hom_ext_of_liftsLocally hE (liftsLocally_twoFibreProductSquare_snd P.fst hbl)
      fun i => ?_
    change (D i).snd ≫ (P.fst ≫ (associatedMap B S hS ψg).1) = (D i).snd ≫ θ
    rw [← discrete_assoc, ← eD i, discrete_assoc, ← associatedMap_comp, hglue i, hψ i]
  · rintro ψ' ⟨η⟩
    have h' : P.fst ≫ (associatedMap B S hS ψ'.hom).1 = θ := hom_eq_of_hom₂ B S hS η.hom
    refine ObjectProperty.hom_ext _ (hom_ext_of_liftsSectionsLocally hbl hE fun i => ?_)
    change (b i).hom ≫ ψ'.hom = (b i).hom ≫ ψg
    rw [hglue i]
    have key := eq_of_isCategoricalModuliSpace B S hS (hDc i) ((D i).snd ≫ θ) (b i ≫ ψ') (ψ i)
      ⟨eqToIso (by
        change (D i).fst ≫ (associatedMap B S hS ((b i).hom ≫ ψ'.hom)).1 = _
        rw [associatedMap_comp, ← discrete_assoc, eD i, discrete_assoc, h'])⟩ ⟨eqToIso (hψ i)⟩
    exact congrArg (·.hom) key

end Pieces

/-! ### The Keel–Mori moduli map -/

namespace KeelMoriCover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {C : KeelMoriCover B S hS 𝒳} (hC : C.IsSmall)

attribute [local instance] hasSheafify_bigFppfOver

/-- **The moduli map of a small Keel–Mori cover is a uniform categorical moduli space.** -/
theorem isUniformCategoricalModuliSpace_moduliMap :
    IsUniformCategoricalModuliSpace B S hS (Msp' hC) (moduliMap hC).hom :=
  isUniformCategoricalModuliSpace_of_pieces (moduliMap hC).hom (uSp hC)
    (fun i => spaceModuliSquare B S hS (M := Msp' hC) (M' := C.Msp i) (C.map i) (moduliMap hC)
      (C.f i) (uSp hC i) (map_comp_moduliMap hC i).symm)
    (fun i => (nonempty_isTwoFibreProduct_square hC i).some)
    (fun i => C.isUniformCategoricalModuliSpace_f i)
    (fun i => Space.isFlat_of_isEtale B S hS (isEtale_u hC i))
    (liftsSectionsLocally_of_exists fun _ m => exists_cover_lift_point hC m)

end KeelMoriCover

end AlgebraicGeometry.Stack

end
