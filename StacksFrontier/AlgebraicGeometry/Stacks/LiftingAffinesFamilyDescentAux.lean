module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSingleDescentGlue
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesDescentMorphisms
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentTransferHom
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Local tests for morphisms of smooth lifts (Stacks 0CJU)

Tools for the descent of smooth lifts along a covering family in the proof of Stacks 0CJU:

* every morphism of smooth lifts is strongly cartesian over the spaces-étale site, so morphisms
  over the same base morphism agree once they agree after a fixed morphism, and morphisms factor
  through any fixed morphism over a factorization of their base;
* morphisms out of a smooth lift whose base has no points are determined by their base;
* two morphisms out of a smooth lift `ω` with the same base agree as soon as they agree after
  every morphism `ω' ⟶ ω` whose base, followed by a fixed `φ : ω.base ⟶ X`, factors through a
  member of a fixed jointly surjective family `{N l ⟶ X}`.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.hom_eq_of_comp_eq`,
  `AlgebraicGeometry.Stack.EtaleSmoothLift.liftThrough`,
  `AlgebraicGeometry.Stack.EtaleSmoothLift.hom_eq_of_isEmpty_points`,
  `AlgebraicGeometry.Stack.EtaleSmoothLift.hom_eq_of_forall_comp_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Points of a fibre product in the spaces-étale site** (Stacks 03H4): two points with the
same image amalgamate to a point of a cartesian square. -/
theorem exists_point_of_isPullback_toSpaces {A Y Z T : SpacesEtale B S hS X} {p : A ⟶ Y}
    {q : A ⟶ Z} {g : Y ⟶ T} {f : Z ⟶ T} (sq : IsPullback p q g f)
    (y : points B S hS Y.obj.left.obj) (z : points B S hS Z.obj.left.obj)
    (h : pointsMap B S hS _ g.hom.left.hom y = pointsMap B S hS _ f.hom.left.hom z) :
    ∃ a : points B S hS A.obj.left.obj,
      pointsMap B S hS _ p.hom.left.hom a = y ∧ pointsMap B S hS _ q.hom.left.hom a = z :=
  Space.exists_point_of_isPullback B S hS (sq.map (toSpaces B S hS X)) y z h

/-- Precomposing with the identification of two equal objects does not change the image of a
point. -/
theorem exists_pointsMap_eqToHom_comp {A A' T : SpacesEtale B S hS X} (h : A' = A) (f : A ⟶ T)
    (a : points B S hS A.obj.left.obj) :
    ∃ a' : points B S hS A'.obj.left.obj,
      pointsMap B S hS _ (eqToHom h ≫ f).hom.left.hom a' = pointsMap B S hS _ f.hom.left.hom a := by
  subst h
  exact ⟨a, by rw [eqToHom_refl, Category.id_comp]⟩

end AlgebraicGeometry.Space.SpacesEtale

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

namespace EtaleSmoothLift

/-- **The projection of smooth lifts is a fibred category**, from
`AlgebraicGeometry.Stack.EtaleSmoothLift.isFiberedInGroupoids_proj` (Stacks 0CJT). -/
theorem isFibered_proj : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsFibered :=
  isFiberedInGroupoids_proj.isFibered

/-- A morphism of smooth lifts lies over its base component. -/
theorem isHomLift_base {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : ξ ⟶ η) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (Hom.base m) m :=
  IsHomLift.map (p := proj) m

/-- A morphism of smooth lifts lying over a morphism between their bases has that base
component. -/
theorem base_eq_of_isHomLift {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : ξ ⟶ η)
    {f : ξ.base ⟶ η.base} (h : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift f m) :
    Hom.base m = f := by
  have e := IsHomLift.fac' (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) f m
  change Hom.base m = eqToHom rfl ≫ f ≫ eqToHom rfl at e
  simpa using e

/-- A morphism of smooth lifts lying over a morphism into the base of its target has base
component that morphism, up to the identification of the base of its source. -/
theorem base_eq_eqToHom_comp {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : ξ ⟶ η)
    {V : Space.SpacesEtale B S hS W} {g : V ⟶ η.base}
    (h : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g m) :
    Hom.base m = eqToHom (@IsHomLift.domain_eq _ _ _ _ proj _ _ _ _ g m h) ≫ g := by
  have e := @IsHomLift.fac' _ _ _ _ proj _ _ _ _ g m h
  change Hom.base m = eqToHom _ ≫ g ≫ eqToHom rfl at e
  rw [eqToHom_refl, Category.comp_id] at e
  exact e

/-- A morphism of smooth lifts lies over its base component followed by an identification. -/
theorem isHomLift_base_comp_eqToHom {ξ η : EtaleSmoothLift B S hS ι hι W x hx} (m : ξ ⟶ η)
    {V : Space.SpacesEtale B S hS W} (e : η.base = V) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (Hom.base m ≫ eqToHom e) m := by
  subst e
  rw [eqToHom_refl, Category.comp_id]
  exact isHomLift_base m

/-- **Morphisms over the same base morphism agree once they agree after a fixed morphism**: every
morphism of smooth lifts is strongly cartesian. -/
theorem hom_eq_of_comp_eq {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {V : Space.SpacesEtale B S hS W} {g : V ⟶ η.base} {χ₁ χ₂ : ω ⟶ η}
    (h₁ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g χ₁)
    (h₂ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g χ₂)
    (h : χ₁ ≫ φ = χ₂ ≫ φ) : χ₁ = χ₂ :=
  @Functor.IsStronglyCartesian.ext _ _ _ _ proj _ _ _ _ (proj.map φ) φ
    (isFiberedInGroupoids_proj.isStronglyCartesian φ) _ _ g χ₁ χ₂ h₁ h₂ h

/-- **A morphism factors through a fixed morphism over a factorization of its base**: the
factorization, from the strong cartesianness of `φ`. -/
def liftThrough {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {V : Space.SpacesEtale B S hS W} (g : V ⟶ η.base) (ψ : ω ⟶ ξ)
    (hψ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (g ≫ Hom.base φ) ψ) :
    ω ⟶ η :=
  @Functor.IsStronglyCartesian.map _ _ _ _ proj _ _ _ _ (proj.map φ) φ
    (isFiberedInGroupoids_proj.isStronglyCartesian φ) _ _ g (g ≫ Hom.base φ) rfl ψ hψ

/-- The factorization lies over `g`. -/
theorem isHomLift_liftThrough {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {V : Space.SpacesEtale B S hS W} (g : V ⟶ η.base) (ψ : ω ⟶ ξ)
    (hψ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (g ≫ Hom.base φ) ψ) :
    (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g (liftThrough φ g ψ hψ) :=
  @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ proj _ _ _ _ (proj.map φ) φ
    (isFiberedInGroupoids_proj.isStronglyCartesian φ) _ _ g (g ≫ Hom.base φ) rfl ψ hψ

/-- The factorization followed by `φ` is `ψ`. -/
theorem liftThrough_comp {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {V : Space.SpacesEtale B S hS W} (g : V ⟶ η.base) (ψ : ω ⟶ ξ)
    (hψ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (g ≫ Hom.base φ) ψ) :
    liftThrough φ g ψ hψ ≫ φ = ψ :=
  @Functor.IsStronglyCartesian.fac _ _ _ _ proj _ _ _ _ (proj.map φ) φ
    (isFiberedInGroupoids_proj.isStronglyCartesian φ) _ _ g (g ≫ Hom.base φ) rfl ψ hψ

/-- `AlgebraicGeometry.Stack.EtaleSmoothLift.hom_eq_of_comp_eq` for a morphism given as lying
over a morphism `fφ` of the spaces-étale site. -/
theorem hom_eq_of_comp_eq_of_isHomLift {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {Vη Vξ : Space.SpacesEtale B S hS W} {fφ : Vη ⟶ Vξ}
    (hφ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift fφ φ)
    {V : Space.SpacesEtale B S hS W} {g : V ⟶ Vη} {χ₁ χ₂ : ω ⟶ η}
    (h₁ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g χ₁)
    (h₂ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g χ₂)
    (h : χ₁ ≫ φ = χ₂ ≫ φ) : χ₁ = χ₂ :=
  @Functor.IsStronglyCartesian.ext _ _ _ _ proj _ _ _ _ fφ φ
    (@Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ proj
      isFiberedInGroupoids_proj _ _ _ _ fφ φ hφ) _ _ g χ₁ χ₂ h₁ h₂ h

/-- **A morphism factors through a morphism lying over `fφ` over any factorization of its
base through `fφ`.** -/
theorem exists_lift_of_isHomLift {ξ η ω : EtaleSmoothLift B S hS ι hι W x hx} (φ : η ⟶ ξ)
    {Vη Vξ : Space.SpacesEtale B S hS W} {fφ : Vη ⟶ Vξ}
    (hφ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift fφ φ)
    {V : Space.SpacesEtale B S hS W} (g : V ⟶ Vη) (ψ : ω ⟶ ξ)
    (hψ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift (g ≫ fφ) ψ) :
    ∃ χ : ω ⟶ η, (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).IsHomLift g χ ∧ χ ≫ φ = ψ :=
  have hs := @Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift _ _ _ _ proj
    isFiberedInGroupoids_proj _ _ _ _ fφ φ hφ
  ⟨@Functor.IsStronglyCartesian.map _ _ _ _ proj _ _ _ _ fφ φ hs _ _ g (g ≫ fφ) rfl ψ hψ,
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ proj _ _ _ _ fφ φ hs _ _ g (g ≫ fφ) rfl
      ψ hψ,
    @Functor.IsStronglyCartesian.fac _ _ _ _ proj _ _ _ _ fφ φ hs _ _ g (g ≫ fφ) rfl ψ hψ⟩

/-- **Morphisms out of a smooth lift whose base has no points are determined by their base
component**: the gluing of morphisms along the empty family, which covers. -/
theorem hom_eq_of_isEmpty_points {ω η : EtaleSmoothLift B S hS ι hι W x hx}
    (h : IsEmpty (Space.points B S hS ω.base.obj.left.obj)) (χ₁ χ₂ : ω ⟶ η)
    (hb : Hom.base χ₁ = Hom.base χ₂) : χ₁ = χ₂ := by
  obtain ⟨g, -, hg⟩ := existsUnique_hom_of_jointlySurjective (ξ := ω) (η := η)
    (K := PEmpty.{1}) (ζ := fun k => k.elim) (fun k => k.elim) (fun q => (h.false q).elim)
    (fun k => k.elim) (Hom.base χ₁) (fun k => k.elim) (fun k => k.elim)
  exact (hg χ₁ ⟨rfl, fun k => k.elim⟩).trans (hg χ₂ ⟨hb.symm, fun k => k.elim⟩).symm

/-- **The local test along a jointly surjective family.** Let `{ιX l : N l ⟶ X}` be jointly
surjective on points and `φ : ω.base ⟶ X`. Two morphisms out of `ω` with the same base
component agree as soon as they agree after every morphism `t : ω' ⟶ ω` such that
`t.base ≫ φ` factors through some `ιX l`: the pullbacks of the family along `φ` cover
`ω.base` (Stacks 03H4), the morphisms lift to smooth lifts, and morphisms glue uniquely along
coverings (condition (2) of Stacks 02ZI). -/
theorem hom_eq_of_forall_comp_eq {ω η : EtaleSmoothLift B S hS ι hι W x hx} {L : Type u}
    {N : L → Space.SpacesEtale B S hS W} {X : Space.SpacesEtale B S hS W} (ιX : ∀ l, N l ⟶ X)
    (hcov : ∀ q : Space.points B S hS X.obj.left.obj, ∃ (l : L)
      (y : Space.points B S hS (N l).obj.left.obj),
        Space.pointsMap B S hS _ (ιX l).hom.left.hom y = q)
    (φ : ω.base ⟶ X) {g g' : ω ⟶ η} (hb : Hom.base g = Hom.base g')
    (h : ∀ (l : L) (ω' : EtaleSmoothLift B S hS ι hι W x hx) (t : ω' ⟶ ω)
      (v : ω'.base ⟶ N l), Hom.base t ≫ φ = v ≫ ιX l → t ≫ g = t ≫ g') : g = g' := by
  classical
  choose ω' t hω' ht using fun l => exists_hom_base_eq ω (pullback.fst φ (ιX l))
  have hm : ∀ q : Space.points B S hS ω.base.obj.left.obj, ∃ (l : L)
      (r : Space.points B S hS (ω' l).base.obj.left.obj),
        Space.pointsMap B S hS _ (Hom.base (t l)).hom.left.hom r = q := by
    intro q
    obtain ⟨l, y, hy⟩ := hcov (Space.pointsMap B S hS _ φ.hom.left.hom q)
    obtain ⟨a, ha, -⟩ := Space.SpacesEtale.exists_point_of_isPullback_toSpaces
      (IsPullback.of_hasPullback φ (ιX l)) q y hy.symm
    obtain ⟨r, hr⟩ := Space.SpacesEtale.exists_pointsMap_eqToHom_comp (hω' l)
      (pullback.fst φ (ιX l)) a
    exact ⟨l, r, by rw [ht l, hr, ha]⟩
  obtain ⟨gl, -, huniq⟩ := existsUnique_hom_of_jointlySurjective (ξ := ω) (η := η) (K := L)
    (ζ := ω') t hm (fun l => t l ≫ g) (Hom.base g) (fun l => rfl)
    (fun k l ω'' a b _ hab => by rw [← Category.assoc, hab, Category.assoc])
  refine (huniq g ⟨rfl, fun l => rfl⟩).trans (huniq g' ⟨hb.symm, fun l => ?_⟩).symm
  refine (h l (ω' l) (t l) (eqToHom (hω' l) ≫ pullback.snd φ (ιX l)) ?_).symm
  rw [ht l, Category.assoc, pullback.condition, Category.assoc]

end EtaleSmoothLift

end AlgebraicGeometry.Stack
