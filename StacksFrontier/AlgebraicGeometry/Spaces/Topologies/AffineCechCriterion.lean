module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.Data.Fin.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Affine objects suffice for Čech-local properties on the big fppf site of a space

Let `X` be an algebraic space over a scheme `S`. A property of the objects of the big fppf
site `(Spaces/X)` which descends along every fppf covering from the covering's iterated fibre
products holds for `X` as soon as it holds for every affine object flat and locally of finite
presentation over `X`.

## Main results

* `AlgebraicGeometry.Space.holds_of_affine_of_cechLocal`: **Stacks 0DK6**.

## Implementation notes

The iterated fibre products `U_{i_0} ×_U … ×_U U_{i_p}` of a covering family are described by
limit cones over a wide cospan of `p + 1` legs, so the descent hypothesis is independent of a
choice of fibre product. The reduction runs in two steps, as in the source: first for an object
with separated underlying space, covered by its affine opens, then for `X` itself, covered by
an étale atlas whose iterated fibre products are separated.

Both steps are instances of one lemma, `cech_of_affineOpen_cover`, applied to the covering of a
represented object by its affine opens with a multiplicative, base-change stable class `M` of
open immersions controlling the shape of the members: `M` is `IsOpenImmersion ⊓ IsAffineHom`
for the first step and `IsOpenImmersion` for the second.

## References

* [Stacks Project, Tag 0DK6](https://stacks.math.columbia.edu/tag/0DK6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry.Space


/-- The wide pullback cone on `f : Y i ⟶ Z`, `i : Fin (n + 2)`, assembled from a cone on the
last `n + 1` legs together with a commuting square over the first leg. -/
private abbrev consCone {C : Type u} [Category.{v} C] {n : ℕ}
    {Z : C} {Y : Fin (n + 2) → C} {f : ∀ i, Y i ⟶ Z}
    (d : WidePullbackCone (fun i : Fin (n + 1) => f i.succ))
    {W : C} (p : W ⟶ d.pt) (q : W ⟶ Y 0)
    (h : p ≫ d.base = q ≫ f 0) : WidePullbackCone f :=
  WidePullbackCone.mk (q ≫ f 0) (Fin.cases q (fun i => p ≫ d.π i)) (by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · change (p ≫ d.π i) ≫ f i.succ = _
      rw [Category.assoc, d.condition]
      exact h)
/-- The cone assembled by `consCone` is a limit cone when the cone on the last `n + 1` legs is
a limit and the square over the first leg is cartesian. -/
private noncomputable def consConeIsLimit {C : Type u} [Category.{v} C] {n : ℕ}
    {Z : C} {Y : Fin (n + 2) → C} {f : ∀ i, Y i ⟶ Z}
    (d : WidePullbackCone (fun i : Fin (n + 1) => f i.succ)) (hd : IsLimit d)
    {W : C} (p : W ⟶ d.pt) (q : W ⟶ Y 0)
    (h : IsPullback p q d.base (f 0)) : IsLimit (consCone d p q h.w) := by
  let tail (t : WidePullbackCone f) : t.pt ⟶ d.pt :=
    WidePullbackCone.IsLimit.lift hd t.base (fun i => t.π i.succ) (fun i => t.condition _)
  have tail_base (t : WidePullbackCone f) : tail t ≫ d.base = t.base := by
    apply WidePullbackCone.IsLimit.lift_base
  have tail_π (t : WidePullbackCone f) (i : Fin (n + 1)) :
      tail t ≫ d.π i = t.π i.succ := by apply WidePullbackCone.IsLimit.lift_π
  let lift (t : WidePullbackCone f) := h.lift (tail t) (t.π 0)
    ((tail_base t).trans (t.condition 0).symm)
  have lp (t : WidePullbackCone f) : lift t ≫ p = tail t := h.lift_fst _ _ _
  have lq (t : WidePullbackCone f) : lift t ≫ q = t.π 0 := h.lift_snd _ _ _
  apply WidePullbackCone.IsLimit.mk _ lift
  · intro t
    change lift t ≫ (q ≫ f 0) = t.base
    rw [← Category.assoc, lq, t.condition]
  · intro t i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact lq t
    · change lift t ≫ (p ≫ d.π i) = _
      rw [← Category.assoc, lp, tail_π]
  · intro t m hb hm
    change t.pt ⟶ W at m
    dsimp [consCone] at hb hm
    apply h.hom_ext
    · rw [lp]
      apply WidePullbackCone.IsLimit.hom_ext hd
      · rw [tail_base, Category.assoc, h.w]
        exact hb
      · intro i
        rw [tail_π, Category.assoc]
        exact hm i.succ
    · rw [lq]
      exact hm 0

/-- A finite family of morphisms into an object of `D` whose members are `M`-relative along a
fully faithful `F` has a wide pullback represented in `C`; its base is again `M`-relative and
its first projection has `M`. -/
private theorem exists_represented_widePullback
    {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    (F : C ⥤ D) [F.Full] [F.Faithful] [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F]
    (M : MorphismProperty C) [M.IsMultiplicative] [M.IsStableUnderBaseChange]
    {Z : D} (n : ℕ) (Y : Fin (n + 1) → C) (f : ∀ i, F.obj (Y i) ⟶ Z)
    (hf : ∀ i, M.relative F (f i)) :
    ∃ (W : C) (b : F.obj W ⟶ Z) (p : ∀ i, W ⟶ Y i)
      (h : ∀ i, F.map (p i) ≫ f i = b),
      Nonempty (IsLimit (WidePullbackCone.mk b (fun i => F.map (p i)) h)) ∧
      M.relative F b ∧ M (p 0) := by
  induction n with
  | zero =>
    change (Fin 1 → C) at Y
    change (∀ i : Fin 1, F.obj (Y i) ⟶ Z) at f
    let p : ∀ i : Fin 1, Y 0 ⟶ Y i := fun i => eqToHom (by congr 1; exact Subsingleton.elim _ _)
    have h (i : Fin 1) : F.map (p i) ≫ f i = f 0 := by
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [p]
    refine ⟨Y 0, f 0, p, h, ⟨?_⟩, hf 0, ?_⟩
    · apply WidePullbackCone.IsLimit.mk _ (fun t => t.π 0)
      · intro t
        exact t.condition 0
      · intro t i
        change Fin 1 at i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        show t.π 0 ≫ F.map (p 0) = t.π 0
        simp [p]
      · intro t m hb hm
        change t.pt ⟶ F.obj (Y 0) at m
        have hm0 := hm 0
        change m ≫ F.map (p 0) = t.π 0 at hm0
        show m = t.π 0
        simpa [p] using hm0
    · simpa [p] using M.id_mem (Y 0)
  | succ n ih =>
    obtain ⟨W, b, p, hp, ⟨hd⟩, hb, _⟩ := ih (fun i => Y i.succ)
      (fun i => f i.succ) (fun i => hf i.succ)
    let r := hb.rep.fst' (f 0)
    let q := hb.rep.snd (f 0)
    have H := hb.rep.isPullback' (f 0)
    let p' : ∀ i, hb.rep.pullback (f 0) ⟶ Y i := Fin.cases q (fun i => r ≫ p i)
    have hp' (i) : F.map (p' i) ≫ f i = F.map q ≫ f 0 := by
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simpa [p', Functor.map_comp, Category.assoc, hp, r, q] using H.w
    have hq : M q := hb.property_snd (f 0)
    refine ⟨_, F.map q ≫ f 0, p', hp', ⟨?_⟩,
      (M.relative F).comp_mem _ _ (MorphismProperty.relative_map hq) (hf 0), hq⟩
    convert consConeIsLimit (WidePullbackCone.mk b (fun i => F.map (p i)) hp)
      hd (f := f) (F.map r) (F.map q) H using 1
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [p']
    · simp [p', Functor.map_comp]
      rfl

/-- The cone of underlying presheaf morphisms of a wide pullback cone in a slice of the
category of algebraic spaces. -/
private def underlyingCone {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S)
    {X : T.Spaces} {ι : Type*} {U : Over X} {Y : ι → Over X}
    {f : ∀ i, Y i ⟶ U} (c : WidePullbackCone f) :
    WidePullbackCone (fun i => (f i).left.hom) :=
  WidePullbackCone.mk c.base.left.hom (fun i => (c.π i).left.hom) (fun i => by
    exact congrArg (fun a => a.left.hom) (c.condition i))
/-- A wide pullback cone of the underlying presheaf morphisms whose vertex is an algebraic
space, read back as a cone in the slice. -/
private def liftCone {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S)
    {X : T.Spaces} {ι : Type*} {U : Over X} {Y : ι → Over X}
    {f : ∀ i, Y i ⟶ U} (d : WidePullbackCone (fun i => (f i).left.hom))
    (hAlg : AlgebraicGeometry.IsAlgebraicSpace T.schemeSite S T.scheme_mem d.pt) :
    WidePullbackCone f := by
  let W : T.Spaces := ⟨d.pt, hAlg⟩
  let V : Over X := Over.mk (ObjectProperty.homMk (X := W) (Y := X)
    (d.base ≫ U.hom.hom))
  let b : V ⟶ U := Over.homMk (ObjectProperty.homMk d.base) (by rfl)
  let p (i) : V ⟶ Y i := Over.homMk (ObjectProperty.homMk (d.π i)) (by
    apply ObjectProperty.hom_ext
    change d.π i ≫ (Y i).hom.hom = d.base ≫ U.hom.hom
    have w := congrArg (fun a => a.hom) (f i).w
    change (f i).left.hom ≫ U.hom.hom = (Y i).hom.hom at w
    rw [← w, ← Category.assoc, d.condition])
  exact WidePullbackCone.mk b p (fun i => by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact d.condition i)
/-- Reading a limit cone of underlying presheaf morphisms back into the slice gives a limit
cone. -/
private noncomputable def liftConeIsLimit {S : Scheme.{u}}
    (T : AlgebraicGeometry.BigFppfSpaceSite S)
    {X : T.Spaces} {ι : Type*} {U : Over X} {Y : ι → Over X}
    {f : ∀ i, Y i ⟶ U} (d : WidePullbackCone (fun i => (f i).left.hom))
    (hAlg : AlgebraicGeometry.IsAlgebraicSpace T.schemeSite S T.scheme_mem d.pt)
    (hd : IsLimit d) : IsLimit (liftCone T d hAlg) := by
  let k (s : WidePullbackCone f) := hd.lift (underlyingCone T s)
  have kb (s : WidePullbackCone f) : k s ≫ d.base = s.base.left.hom :=
    hd.fac _ none
  have kp (s : WidePullbackCone f) (i) : k s ≫ d.π i = (s.π i).left.hom :=
    hd.fac _ (some i)
  let l (s : WidePullbackCone f) : s.pt ⟶ (liftCone T d hAlg).pt :=
    Over.homMk (ObjectProperty.homMk (k s)) (by
      apply ObjectProperty.hom_ext
      change k s ≫ (d.base ≫ U.hom.hom) = s.pt.hom.hom
      rw [← Category.assoc, kb]
      exact congrArg (fun a => a.hom) s.base.w)
  apply WidePullbackCone.IsLimit.mk _ l
  · intro s
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact kb s
  · intro s i
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact kp s i
  · intro s m hb hp
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply WidePullbackCone.IsLimit.hom_ext hd
    · exact (congrArg (fun a => a.left.hom) hb).trans (kb s).symm
    · intro i
      exact (congrArg (fun a => a.left.hom) (hp i)).trans (kp s i).symm

/-- Isomorphisms of the sources of a wide cospan compatible with its legs induce an
isomorphism of the wide cospan diagrams. -/
private def wideCospanIsoOfIso {C : Type u} [Category.{v} C] {ι : Type w}
    {Z : C} {Y Y' : ι → C} {f : ∀ i, Y i ⟶ Z} {g : ∀ i, Y' i ⟶ Z}
    (hY : ∀ i, Y i ≅ Y' i)
    (hf : ∀ i, f i = (hY i).hom ≫ g i) :
    WidePullbackShape.wideCospan Z Y f ≅ WidePullbackShape.wideCospan Z Y' g := by
  refine NatIso.ofComponents (fun j => ?_) ?_
  · cases j with
    | none => exact Iso.refl Z
    | some i => exact hY i
  · intro j j' a
    casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _) <;>
      simp [WidePullbackShape.wideCospan, hf]

/-- An affine open of a big fppf object is small enough to be an object of the site. -/
private theorem contains_affineOpen
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    B.Contains V.1.toScheme :=
  (Scheme.size_coe_opens_le _ V.1).trans_lt T.left.2

private noncomputable def affineOpenObject
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    AlgebraicGeometry.BigFppfOver B S hS := by
  let m : B.obj (contains_affineOpen B S hS T V) ⟶ T.left := B.inclusion.preimage V.1.ι
  exact Over.mk (m ≫ T.hom)

private noncomputable def affineOpenInclusion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    affineOpenObject B S hS T V ⟶ T := by
  let m : B.inclusion.obj (B.obj (contains_affineOpen B S hS T V)) ⟶
    B.inclusion.obj T.left := V.1.ι
  exact Over.homMk (B.inclusion.preimage m) (by simp [affineOpenObject, m])

private theorem affineOpenInclusion_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (V : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens) :
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map
        (affineOpenInclusion B S hS T V) = V.1.ι := by
  let vhom : B.inclusion.obj (B.obj (contains_affineOpen B S hS T V)) ⟶
    B.inclusion.obj T.left := V.1.ι
  show B.inclusion.map (B.inclusion.preimage vhom) = vhom
  exact B.inclusion.map_preimage vhom

private theorem affineOpen_fieldPoint_factors
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicGeometry.BigFppfOver B S hS}
    (V : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj T))
    (hp : AlgebraicGeometry.Space.schemePoint B S hS T p ∈
      (V.1 : Set ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T))) :
    ∃ q : AlgebraicGeometry.Space.FieldValuedPoint B S hS
        (yoneda.obj (affineOpenObject B S hS T V)),
      AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj (affineOpenObject B S hS T V))
        (yoneda.map (affineOpenInclusion B S hS T V))
        (q.class B S hS (yoneda.obj (affineOpenObject B S hS T V))) =
          p.class B S hS (yoneda.obj T) := by
  classical
  let Q := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let A := AlgebraicGeometry.Space.FieldValuedPoint.siteObject B S hS (yoneda.obj T) p
  let : Field p.carrier := p.field
  have hrange : Set.range (Q.map p.value) ⊆
      Set.range (Q.map (affineOpenInclusion B S hS T V)) := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    have hz : z = IsLocalRing.closedPoint p.carrier := by
      exact (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
    subst z
    let : AlgebraicGeometry.IsOpenImmersion V.1.ι := inferInstance
    have hmem : Q.map p.value (IsLocalRing.closedPoint p.carrier) ∈
        (V.1 : Set (Q.obj T)) := by
      simpa [AlgebraicGeometry.Space.schemePoint, Q] using hp
    have hopen : Q.map p.value (IsLocalRing.closedPoint p.carrier) ∈
        (V.1.ι).opensRange := by
      rw [Scheme.Opens.opensRange_ι]
      exact hmem
    rcases (Scheme.Hom.mem_opensRange).mp hopen with ⟨z, hz⟩
    exact ⟨z, by rw [affineOpenInclusion_map]; exact hz⟩
  let : AlgebraicGeometry.IsOpenImmersion (Q.map (affineOpenInclusion B S hS T V)) := by
    exact (affineOpenInclusion_map B S hS T V).symm ▸
      (inferInstance : AlgebraicGeometry.IsOpenImmersion V.1.ι)
  let ψ : Spec (.of p.carrier) ⟶
      Q.obj (affineOpenObject B S hS T V) :=
    AlgebraicGeometry.IsOpenImmersion.lift (Q.map (affineOpenInclusion B S hS T V))
      (Q.map p.value) hrange
  have hψ : ψ ≫ Q.map (affineOpenInclusion B S hS T V) = Q.map p.value :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let k : A.left ⟶ (affineOpenObject B S hS T V).left :=
    B.inclusion.preimage
      (show B.inclusion.obj A.left ⟶
        B.inclusion.obj (affineOpenObject B S hS T V).left from ψ)
  have hk : B.inclusion.map k = ψ := by
    show B.inclusion.map
      (B.inclusion.preimage
        (show B.inclusion.obj A.left ⟶
          B.inclusion.obj (affineOpenObject B S hS T V).left from ψ)) = ψ
    rw [B.inclusion.map_preimage]
  let g : A ⟶ affineOpenObject B S hS T V := Over.homMk k (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp]
    have hj : Q.map (affineOpenInclusion B S hS T V) ≫
        B.inclusion.map T.hom = B.inclusion.map (affineOpenObject B S hS T V).hom := by
      show B.inclusion.map (affineOpenInclusion B S hS T V).left ≫
        B.inclusion.map T.hom = B.inclusion.map (affineOpenObject B S hS T V).hom
      rw [← B.inclusion.map_comp, (affineOpenInclusion B S hS T V).w]
    have hpv : Q.map p.value ≫ B.inclusion.map T.hom = B.inclusion.map A.hom := by
      show B.inclusion.map p.value.left ≫ B.inclusion.map T.hom =
        B.inclusion.map A.hom
      rw [← B.inclusion.map_comp, p.value.w]
      rfl
    rw [hk, ← hj, ← Category.assoc, hψ]
    exact hpv)
  have hg : g ≫ affineOpenInclusion B S hS T V = p.value := by
    apply Over.OverMorphism.ext
    have hleft : k ≫ (affineOpenInclusion B S hS T V).left = p.value.left := by
      apply B.inclusion.map_injective
      rw [B.inclusion.map_comp, hk]
      show ψ ≫ Q.map (affineOpenInclusion B S hS T V) = Q.map p.value
      exact hψ
    exact hleft
  let q : AlgebraicGeometry.Space.FieldValuedPoint B S hS
      (yoneda.obj (affineOpenObject B S hS T V)) :=
    ⟨p.carrier, p.contained, p.toBase, g⟩
  refine ⟨q, ?_⟩
  rw [AlgebraicGeometry.Space.pointsMap_class]
  have hmap : AlgebraicGeometry.Space.FieldValuedPoint.map B S hS
      (yoneda.obj (affineOpenObject B S hS T V))
      (yoneda.map (affineOpenInclusion B S hS T V)) q = p := by
    cases p
    simp [q, AlgebraicGeometry.Space.FieldValuedPoint.map, hg]
  exact congrArg (AlgebraicGeometry.Space.FieldValuedPoint.class B S hS (yoneda.obj T)) hmap

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

private theorem inverseImage_stable
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (M : MorphismProperty Scheme.{u}) [M.IsStableUnderBaseChange] :
    (M.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  constructor
  intro A B' C D f g p q h hg
  exact MorphismProperty.of_isPullback (P := M)
    (h.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hg

attribute [local instance] inverseImage_stable

private theorem affineOpen_yoneda_cover
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS) :
    AlgebraicGeometry.Space.IsZariskiCovering B S hS
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj T).affineOpens
      (fun V => yoneda.obj (affineOpenObject B S hS T V))
      (fun V => yoneda.map (affineOpenInclusion B S hS T V)) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) G
  refine ⟨?_, ?_⟩
  · intro V
    show Q.presheaf (yoneda.map (affineOpenInclusion B S hS T V))
    apply (MorphismProperty.relative_map_iff (P := Q)).2
    show AlgebraicGeometry.IsOpenImmersion (G.map (affineOpenInclusion B S hS T V))
    exact (affineOpenInclusion_map B S hS T V).symm ▸
      (inferInstance : AlgebraicGeometry.IsOpenImmersion V.1.ι)
  · intro x
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ := G.obj T |>.isBasis_affineOpens.exists_subset_of_mem_open
      (a := AlgebraicGeometry.Space.schemePoint B S hS T p) (by simp) isOpen_univ
    let V : (G.obj T).affineOpens := ⟨V₀, hV₀⟩
    obtain ⟨q, hq⟩ := affineOpen_fieldPoint_factors B S hS V p hxV₀
    exact ⟨V, q.class B S hS (yoneda.obj (affineOpenObject B S hS T V)), hq⟩

private theorem relative_etale_isEtale
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ F)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f) :
    AlgebraicGeometry.Space.IsEtale B S hS f := by
  let E : MorphismProperty Scheme.{u} := @Etale
  let Q := E.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : E.IsStableUnderComposition :=
    (inferInstance : E.IsMultiplicative).toIsStableUnderComposition
  let : Q.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage _
  let : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  intro T φ hφ
  exact Q.presheaf.comp_mem φ f hφ hf

private theorem etale_is_flat_and_locallyOfFinitePresentation
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    AlgebraicGeometry.Space.IsFlat B S hS f ∧
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation B S hS f :=
  ⟨AlgebraicGeometry.Space.isFlat_of_isEtale B S hS hf,
    AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isEtale B S hS hf⟩

private theorem bounded_representative_over
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) (X : T.Spaces)
    (E : Covering.{u + 1, u + 1, u + 2} (Over X))
    (hE : AlgebraicGeometry.Space.IsFppfCoveringFamily T.schemeSite S T.scheme_mem
      ⟨(Over.forget X).obj E.1, E.2.map (Over.forget X)⟩) :
    ∃ (F : Covering (Over X)) (hTarget : F.1 = E.1),
      AlgebraicGeometry.BigFppfSpaceOver.IsCovering T X F ∧
      ∃ (β : F.2.I₀ → E.2.I₀) (e : ∀ j, F.2.X j ≅ E.2.X (β j)),
        ∀ j, (e j).hom ≫ E.2.f (β j) = F.2.f j ≫ eqToHom hTarget := by
  let E₀ : Covering.{u + 1, u + 1, u + 2} T.Spaces :=
    ⟨(Over.forget X).obj E.1, E.2.map (Over.forget X)⟩
  obtain ⟨R, hR, hEquiv⟩ := T.covering_representative E₀ hE
  rcases R with ⟨Rtarget, Rfamily⟩
  change ∃ hTarget : E₀.1 = Rtarget,
      PreZeroHypercover.CombinatoriallyEquivalent (hTarget ▸ E₀.2) Rfamily at hEquiv
  rcases hEquiv with ⟨hTarget, hComb⟩
  change E₀.1 = Rtarget at hTarget
  have hindex : (hTarget ▸ E₀.2).I₀ = E.2.I₀ := by cases hTarget; rfl
  subst Rtarget
  obtain ⟨β, hX, hf⟩ := hComb.2
  let β' : Rfamily.I₀ → E.2.I₀ := fun j => cast hindex (β j)
  have hX' (j : Rfamily.I₀) : Rfamily.X j =
      (E.2.map (Over.forget X)).X (β' j) := by
    cases hindex
    exact hX j
  have hf' (j : Rfamily.I₀) : Rfamily.f j = eqToHom (hX' j) ≫
      (E.2.map (Over.forget X)).f (β' j) := by
    cases hindex
    exact hf j
  have hX'' (j : Rfamily.I₀) : Rfamily.X j = (E.2.X (β' j)).left := by
    simpa [PreZeroHypercover.map, Over.forget] using hX' j
  have hf'' (j : Rfamily.I₀) : Rfamily.f j =
      eqToHom (hX'' j) ≫ (E.2.f (β' j)).left := by
    have hh := hf' j
    change Rfamily.f j = eqToHom (hX' j) ≫
      (Over.forget X).map (E.2.f (β' j)) at hh
    rw [Over.forget_map] at hh
    have he : hX' j = hX'' j := Subsingleton.elim _ _
    rw [he] at hh
    exact hh
  let F : Covering (Over X) := ⟨E.1, {
    I₀ := Rfamily.I₀
    X j := Over.mk (Rfamily.f j ≫ E.1.hom)
    f j := Over.homMk (Rfamily.f j) (by simp) }⟩
  refine ⟨F, rfl, ?_, β', ?_, ?_⟩
  · show T.IsCovering
      ⟨(Over.forget X).obj E.1, Rfamily⟩
    exact hR
  · intro j
    let eL : (F.2.X j).left ≅ (E.2.X (β' j)).left := eqToIso (hX'' j)
    refine Over.isoMk eL ?_
    show eqToHom (hX'' j) ≫ (E.2.X (β' j)).hom =
      Rfamily.f j ≫ E.1.hom
    calc
      eqToHom (hX'' j) ≫ (E.2.X (β' j)).hom =
          eqToHom (hX'' j) ≫ (E.2.f (β' j)).left ≫ E.1.hom := by
            rw [← Over.w (E.2.f (β' j))]
      _ = Rfamily.f j ≫ E.1.hom := by
        rw [← Category.assoc, ← hf'' j]
  · intro j
    apply Over.OverMorphism.ext
    show (eqToHom (hX'' j) ≫ (E.2.f (β' j)).left) = Rfamily.f j
    rw [← hf'' j]

private theorem cech_of_covering
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) (X : T.Spaces)
    (P : Over X → Prop)
    (hcech : ∀ (E : Covering (Over X)),
      AlgebraicGeometry.BigFppfSpaceOver.IsCovering T X E →
      (∀ (n : ℕ) (i : Fin (n + 1) → E.2.I₀)
        (c : WidePullbackCone (fun k : Fin (n + 1) => E.2.f (i k))),
        IsLimit c → P c.pt) → P E.1)
    (E : Covering.{u + 1, u + 1, u + 2} (Over X))
    (hE : AlgebraicGeometry.Space.IsFppfCoveringFamily T.schemeSite S T.scheme_mem
      ⟨E.1.left, E.2.map (Over.forget X)⟩)
    (hP : ∀ (n : ℕ) (i : Fin (n + 1) → E.2.I₀)
      (c : WidePullbackCone (fun k => E.2.f (i k))), IsLimit c → P c.pt) :
    P E.1 := by
  obtain ⟨F, heq, hF, β, e, he⟩ := bounded_representative_over T X E hE
  rcases E with ⟨U, E⟩
  change F.1 = U at heq
  subst U
  apply hcech F hF
  intro n i c hc
  let α := wideCospanIsoOfIso (fun k => e (i k)) (fun k => by
    simpa using (he (i k)).symm)
  exact hP n (fun k => β (i k)) ((Cone.postcompose α.hom).obj c)
    ((IsLimit.postcomposeHomEquiv α c).symm hc)

private noncomputable def schemeFamilyCover
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) {X : T.Spaces}
    (U : Over X) {I : Type (u + 2)} (Y : I → T.Schemes)
    (f : ∀ i, yoneda.obj (Y i) ⟶ U.left.1) : Covering (Over X) :=
  ⟨U, {
    I₀ := I
    X i := Over.mk (ObjectProperty.homMk
      (X := (AlgebraicGeometry.schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj (Y i))
      (Y := X) (f i ≫ U.hom.hom))
    f i := Over.homMk (ObjectProperty.homMk (f i)) (by rfl) }⟩

private theorem cech_of_represented_family
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) (X : T.Spaces)
    (P : Over X → Prop)
    (hcech : ∀ (E : Covering (Over X)),
      AlgebraicGeometry.BigFppfSpaceOver.IsCovering T X E →
      (∀ (n : ℕ) (i : Fin (n + 1) → E.2.I₀)
        (c : WidePullbackCone (fun k : Fin (n + 1) => E.2.f (i k))),
        IsLimit c → P c.pt) → P E.1)
    (M : MorphismProperty Scheme.{u}) [M.IsMultiplicative] [M.IsStableUnderBaseChange]
    (hME : M ≤ @Etale.{u}) (Q : T.Schemes → Prop)
    (hP : ∀ (V : Over X) (A : T.Schemes), Q A →
      (V.left.1 ≅ yoneda.obj A) →
      AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem V.hom.hom →
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
        V.hom.hom → P V)
    (U : Over X) {I : Type (u + 2)} (Y : I → T.Schemes)
    (f : ∀ i, yoneda.obj (Y i) ⟶ U.left.1)
    (hcov : AlgebraicGeometry.Space.IsFppfCovering T.schemeSite S T.scheme_mem
      (fun i => yoneda.obj (Y i)) f)
    (hf : ∀ i, (M.inverseImage
      (AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem)).presheaf (f i))
    (hQ : ∀ (A : T.Schemes) (i : I) (g : A ⟶ Y i),
      M ((AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map g) → Q A)
    (hUF : AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem U.hom.hom)
    (hUL : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
      U.hom.hom) : P U := by
  let E := schemeFamilyCover T U Y f
  apply cech_of_covering T X P hcech E hcov
  intro n i c hc
  let R := M.inverseImage (AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem)
  obtain ⟨A, b, p, hp, ⟨hd⟩, hb, hp0⟩ := exists_represented_widePullback
    yoneda R n (fun k => Y (i k)) (fun k => f (i k)) (fun k => hf (i k))
  let d := WidePullbackCone.mk b (fun k => yoneda.map (p k)) hp
  have hA := AlgebraicGeometry.isAlgebraicSpace_yoneda T.schemeSite S T.scheme_mem A
  let d' := liftCone T (f := fun k => E.2.f (i k)) d hA
  let e : c.pt ≅ d'.pt := IsLimit.conePointUniqueUpToIso hc
    (liftConeIsLimit T (f := fun k => E.2.f (i k)) d hA hd)
  let J := Over.forget X ⋙ ObjectProperty.ι
    (AlgebraicGeometry.IsAlgebraicSpace T.schemeSite S T.scheme_mem)
  let e' : c.pt.left.1 ≅ yoneda.obj A := J.mapIso e
  have hbe : (MorphismProperty.inverseImage (@Etale.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem)).presheaf b :=
    MorphismProperty.relative_monotone (fun _ _ g hg => hME _ hg) b hb
  have hbf := etale_is_flat_and_locallyOfFinitePresentation U.left.property b
    (relative_etale_isEtale b hbe)
  have hF := AlgebraicGeometry.Space.isFlat_comp T.schemeSite S T.scheme_mem hA U.left.property
    X.property b U.hom.hom hbf.1 hUF
  have hL := AlgebraicGeometry.Space.isLocallyOfFinitePresentation_comp T.schemeSite S T.scheme_mem
    hA U.left.property X.property b U.hom.hom hbf.2 hUL
  have hw : c.pt.hom.hom = e'.hom ≫ (b ≫ U.hom.hom) := by
    exact (congrArg (fun a => a.hom) e.hom.w).symm
  apply hP c.pt A (hQ A (i 0) (p 0) hp0) e'
  · rw [hw]
    exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_precomp_iso T.schemeSite S T.scheme_mem
      (@Flat : MorphismProperty Scheme.{u}) e' (b ≫ U.hom.hom)).mp hF
  · rw [hw]
    exact (AlgebraicGeometry.Space.holdsOnEveryEtaleChart_precomp_iso T.schemeSite S T.scheme_mem
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      e' (b ≫ U.hom.hom)).mp hL

private theorem affineOpen_cover_of_iso
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S)
    (F : T.Spaces) (A : T.Schemes) (e : F.1 ≅ yoneda.obj A) :
    AlgebraicGeometry.Space.IsFppfCovering T.schemeSite S T.scheme_mem
      (fun i : ULift.{u + 2} ((AlgebraicGeometry.BigFppfOver.toScheme
        T.schemeSite S T.scheme_mem).obj A).affineOpens =>
        yoneda.obj (affineOpenObject T.schemeSite S T.scheme_mem A i.down))
      (fun i => yoneda.map (affineOpenInclusion T.schemeSite S T.scheme_mem A i.down)
        ≫ e.inv) := by
  have hcov := affineOpen_yoneda_cover T.schemeSite S T.scheme_mem A
  apply AlgebraicGeometry.Space.isFppfCovering_of_isZariskiCovering _ _ _ F.property
    (fun i => AlgebraicGeometry.isAlgebraicSpace_yoneda _ _ _ _)
  refine ⟨?_, ?_⟩
  · intro i
    exact (MorphismProperty.cancel_right_of_respectsIso _ _ e.inv).2 (hcov.1 i.down)
  · intro x
    obtain ⟨i, z, hz⟩ := hcov.2 (AlgebraicGeometry.Space.pointsMap _ _ _ F.1 e.hom x)
    refine ⟨⟨i⟩, z, ?_⟩
    rw [AlgebraicGeometry.Space.pointsMap_comp_apply, hz,
      ← AlgebraicGeometry.Space.pointsMap_comp_apply, e.hom_inv_id,
      AlgebraicGeometry.Space.pointsMap_id_apply]

private theorem cech_of_affineOpen_cover
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) (X : T.Spaces)
    (P : Over X → Prop)
    (hcech : ∀ (E : Covering (Over X)),
      AlgebraicGeometry.BigFppfSpaceOver.IsCovering T X E →
      (∀ (n : ℕ) (i : Fin (n + 1) → E.2.I₀)
        (c : WidePullbackCone (fun k : Fin (n + 1) => E.2.f (i k))),
        IsLimit c → P c.pt) → P E.1)
    (M : MorphismProperty Scheme.{u}) [M.IsMultiplicative] [M.IsStableUnderBaseChange]
    (hME : M ≤ @Etale.{u}) (Q : T.Schemes → Prop)
    (hP : ∀ (V : Over X) (A : T.Schemes), Q A →
      (V.left.1 ≅ yoneda.obj A) →
      AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem V.hom.hom →
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
        V.hom.hom → P V)
    (U : Over X) (A : T.Schemes) (e : U.left.1 ≅ yoneda.obj A)
    (hM : ∀ V : ((AlgebraicGeometry.BigFppfOver.toScheme
      T.schemeSite S T.scheme_mem).obj A).affineOpens, M V.1.ι)
    (hQ : ∀ (Z : T.Schemes)
      (V : ((AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj A).affineOpens)
      (g : (AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj Z ⟶
        V.1.toScheme),
      M g → Q Z)
    (hUF : AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem U.hom.hom)
    (hUL : AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
      U.hom.hom) : P U := by
  apply cech_of_represented_family T X P hcech M hME Q hP U
    (fun i : ULift.{u + 2} ((AlgebraicGeometry.BigFppfOver.toScheme
      T.schemeSite S T.scheme_mem).obj A).affineOpens =>
        affineOpenObject T.schemeSite S T.scheme_mem A i.down)
    (fun i => yoneda.map (affineOpenInclusion T.schemeSite S T.scheme_mem A i.down) ≫ e.inv)
    (affineOpen_cover_of_iso T U.left A e)
    ?_ ?_ hUF hUL
  · intro i
    apply (MorphismProperty.cancel_right_of_respectsIso _ _ e.inv).2
    apply MorphismProperty.relative_map
    show M ((AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map _)
    rw [affineOpenInclusion_map]
    exact hM i.down
  · intro Z i g hg
    exact hQ Z i.down
      ((AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map g) hg

/-- A Čech-local property of objects of the big fppf site over `X` can be
checked on affine objects flat and locally of finite presentation over `X`. -/
@[stacks 0DK6]
public theorem holds_of_affine_of_cechLocal
    {S : Scheme.{u}} (T : AlgebraicGeometry.BigFppfSpaceSite S) (X : T.Spaces)
    (P : Over X → Prop)
    (hcech : ∀ (E : Covering (Over X)),
      AlgebraicGeometry.BigFppfSpaceOver.IsCovering T X E →
      (∀ (n : ℕ) (i : Fin (n + 1) → E.2.I₀)
        (c : WidePullbackCone (fun k : Fin (n + 1) => E.2.f (i k))),
        IsLimit c → P c.pt) → P E.1)
    (haffine : ∀ U : Over X,
      AlgebraicGeometry.Space.IsAffineSpace T.schemeSite S T.scheme_mem U.left.1 →
      AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem U.hom.hom →
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
        U.hom.hom → P U) :
    P (Over.mk (𝟙 X)) := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme T.schemeSite S T.scheme_mem
  have hsep : ∀ (V : Over X) (A : T.Schemes), Scheme.IsSeparated (G.obj A) →
      (V.left.1 ≅ yoneda.obj A) →
      AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem V.hom.hom →
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
        V.hom.hom → P V := by
    intro V A hA e hF hL
    let : Scheme.IsSeparated (G.obj A) := hA
    let O : MorphismProperty Scheme.{u} := @AlgebraicGeometry.IsOpenImmersion
    let A' : MorphismProperty Scheme.{u} := @AlgebraicGeometry.IsAffineHom
    let : O.IsMultiplicative := inferInstance
    let : A'.IsMultiplicative := inferInstance
    let : (O ⊓ A').IsMultiplicative := MorphismProperty.IsMultiplicative.inf
    let : (O ⊓ A').IsStableUnderBaseChange :=
      MorphismProperty.IsStableUnderBaseChange.inf
    apply cech_of_affineOpen_cover T X P hcech
      (O ⊓ A')
      (fun _ _ f hf => by let : AlgebraicGeometry.IsOpenImmersion f := hf.1; infer_instance)
      (fun A => IsAffine (G.obj A))
      (fun V A hA e => haffine V ⟨A, hA, ⟨e⟩⟩) V A e
      (fun W => ⟨inferInstance, by
        let : IsAffine W.1.toScheme := W.2
        have : AlgebraicGeometry.IsAffineHom (W.1.ι ≫ terminal.from (G.obj A)) := by
          rw [terminal.comp_from]; infer_instance
        exact AlgebraicGeometry.IsAffineHom.of_comp W.1.ι (terminal.from (G.obj A))⟩) ?_ hF hL
    intro Z W g hg
    let : IsAffine W.1.toScheme := W.2
    let : AlgebraicGeometry.IsAffineHom g := hg.2
    exact AlgebraicGeometry.isAffine_of_isAffineHom g
  have hscheme : ∀ (V : Over X) (A : T.Schemes),
      (V.left.1 ≅ yoneda.obj A) →
      AlgebraicGeometry.Space.IsFlat T.schemeSite S T.scheme_mem V.hom.hom →
      AlgebraicGeometry.Space.IsLocallyOfFinitePresentation T.schemeSite S T.scheme_mem
        V.hom.hom → P V := by
    intro V A e hF hL
    apply cech_of_affineOpen_cover T X P hcech
      (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})
      (fun _ _ f hf => by have := hf; infer_instance)
      (fun A => Scheme.IsSeparated (G.obj A)) hsep V A e
      (fun W => inferInstance) ?_ hF hL
    intro Z W g hg
    let : IsAffine W.1.toScheme := W.2
    let : AlgebraicGeometry.IsOpenImmersion g := hg
    constructor
    rw [← terminal.comp_from g]
    infer_instance
  obtain ⟨A, f, hfS, hfE⟩ := X.property.exists_atlas
  have hid : AlgebraicGeometry.Space.IsEtale T.schemeSite S T.scheme_mem (𝟙 X.1) :=
    fun _ _ ha => by simpa using ha
  have hFP := etale_is_flat_and_locallyOfFinitePresentation X.property (𝟙 X.1) hid
  apply cech_of_represented_family T X P hcech (@Etale : MorphismProperty Scheme.{u})
    le_rfl (fun _ => True) (fun V A _ => hscheme V A) (Over.mk (𝟙 X))
    (fun _ : ULift.{u+2} PUnit.{1} => A) (fun _ => f) ?_ (fun _ => hfE)
    (fun _ _ _ _ => trivial) hFP.1 hFP.2
  let hA := AlgebraicGeometry.isAlgebraicSpace_yoneda T.schemeSite S T.scheme_mem A
  have hprops := etale_is_flat_and_locallyOfFinitePresentation X.property f
    (relative_etale_isEtale f hfE)
  refine ⟨X.property, fun _ => AlgebraicGeometry.isAlgebraicSpace_yoneda _ _ _ A,
    fun _ => hprops.1, fun _ => hprops.2, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨z, hz⟩ := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda
    T.schemeSite S T.scheme_mem X.1 X.property A f).mp hfS x
  exact ⟨⟨PUnit.unit⟩, z, hz⟩


end AlgebraicGeometry.Space

end
