module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products along strongly cartesian morphisms (Stacks 06N4)

Let `p : 𝒮 ⥤ 𝒞` present `𝒮` as a category over the base `𝒞`, and let `φ : x ⟶ y`
and `g : z ⟶ y` be morphisms of `𝒮` with `φ` strongly cartesian over its image
`p φ`. Assume the fibre product `p x ×_{p y} p z` exists in `𝒞`, and that we are
given a morphism `a : w ⟶ z` of `𝒮` lying over the second projection
`pr₂ : p x ×_{p y} p z ⟶ p z` and strongly cartesian over it; the hypotheses `hw`
and `ha` are exactly the statement that `p w` is that fibre product and that `p a`
is that projection, transported along `hw`.

Under these assumptions `w` already *is* the fibre product of `x` and `z` over `y`.
Strong cartesianness of `φ` produces a morphism `b : w ⟶ x` lying over the first
projection `pr₁` and satisfying `b ≫ φ = a ≫ g`, because `pr₁ ≫ p φ = pr₂ ≫ p g`
in the base. The resulting square is a limit square: a competing pair
`f' : t ⟶ x`, `k : t ⟶ z` with `f' ≫ φ = k ≫ g` has images forming a cone over
`p φ, p g` in `𝒞`, and the induced morphism `p t ⟶ p x ×_{p y} p z` lifts through
the strongly cartesian `a` to a morphism `u : t ⟶ w` with `u ≫ a = k`; strong
cartesianness of `φ` then forces `u ≫ b = f'`, and both cartesian morphisms
together force `u` to be unique.

Hence `x ×_y z` exists in `𝒮` and is canonically isomorphic to `w`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- The morphism `eqToHom hw ≫ pr₁` lifts through the strongly cartesian morphism `φ`
to a morphism `b : w ⟶ x` with `b ≫ φ = a ≫ g`. -/
private lemma exists_lift_of_pullbackFst
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g)) :
    ∃ b : w ⟶ x,
      b ≫ φ = a ≫ g ∧
      p.map b = eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g) := by
  have heq : p.map (a ≫ g) =
      (eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g)) ≫ p.map φ := by
    simp [p.map_comp, ha, Limits.pullback.condition]
  have : p.IsHomLift (p.map (a ≫ g)) (a ≫ g) := Functor.IsHomLift.map (a ≫ g)
  obtain ⟨b, ⟨_, hb2⟩, _⟩ :=
    Functor.IsStronglyCartesian.universal_property p (p.map φ) φ
      (eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g))
      (p.map (a ≫ g)) heq (a ≫ g)
  refine ⟨b, hb2, ?_⟩
  simpa using IsHomLift.fac' p (eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g)) b

/-- A competing pair `f' : t ⟶ x`, `k : t ⟶ z` with `f' ≫ φ = k ≫ g` induces a
morphism `p t ⟶ p w` in the base, which lifts through the strongly cartesian
morphism `a` to a morphism `u : t ⟶ w` with `u ≫ a = k`. -/
private lemma exists_lift_of_commSq
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g))
    [Functor.IsStronglyCartesian p (p.map a) a]
    {t : 𝒮} (f' : t ⟶ x) (k : t ⟶ z) (hfk : f' ≫ φ = k ≫ g) :
    ∃ u : t ⟶ w,
      u ≫ a = k ∧
      p.map u = Limits.pullback.lift (p.map f') (p.map k)
          (by rw [← Functor.map_comp, ← Functor.map_comp, hfk]) ≫ eqToHom hw.symm := by
  set α : p.obj t ⟶ p.obj w :=
    Limits.pullback.lift (p.map f') (p.map k)
      (by rw [← Functor.map_comp, ← Functor.map_comp, hfk]) ≫ eqToHom hw.symm with hα_def
  have hα_eq : α ≫ p.map a = p.map k := by
    simp [hα_def, ha]
  obtain ⟨u, ⟨_, huComp⟩, _⟩ :=
    Functor.IsStronglyCartesian.universal_property p (p.map a) a
      (R' := p.obj t) (a' := t) α (p.map k) hα_eq.symm k
  exact ⟨u, huComp, (IsHomLift.eq_of_isHomLift p α u).symm⟩

/-- Morphisms into the source of a strongly cartesian morphism are equal if they have the
same image under `p` and the same composite with it. -/
private lemma eq_of_map_eq_of_comp_eq
    (p : 𝒮 ⥤ 𝒞) {x y : 𝒮} (φ : x ⟶ y) [Functor.IsStronglyCartesian p (p.map φ) φ]
    {t : 𝒮} {u u' : t ⟶ x} (hmap : p.map u = p.map u') (h : u ≫ φ = u' ≫ φ) : u = u' := by
  have : p.IsHomLift (p.map u) u := Functor.IsHomLift.map u
  have : p.IsHomLift (p.map u) u' := hmap ▸ Functor.IsHomLift.map u'
  exact Functor.IsStronglyCartesian.ext p (p.map φ) φ (p.map u) h

/-- Two morphisms `t ⟶ w` that agree after composition with both `a` and `b` are equal:
their images agree by the universal property of the pullback in the base, and strong
cartesianness of `a` promotes this to an equality in `𝒮`. -/
private lemma eq_of_comp_eq_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z) (b : w ⟶ x)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g))
    (hb : p.map b = eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g))
    [Functor.IsStronglyCartesian p (p.map a) a]
    {t : 𝒮} {u u' : t ⟶ w}
    (hub : u ≫ b = u' ≫ b) (hua : u ≫ a = u' ≫ a) :
    u = u' := by
  have hpmap : p.map u = p.map u' := by
    refine (cancel_mono (eqToHom hw)).mp (Limits.pullback.hom_ext ?_ ?_)
    · simp [← hb, ← Functor.map_comp, hub]
    · simp [← ha, ← Functor.map_comp, hua]
  exact eq_of_map_eq_of_comp_eq p a hpmap hua

/-- The lift `u` produced by `exists_lift_of_commSq` also factors `f'` through `b`, by
uniqueness in the universal property of the strongly cartesian morphism `φ`. -/
private lemma lift_comp_eq_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z) (b : w ⟶ x)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (hb : p.map b = eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g))
    (hba : b ≫ φ = a ≫ g)
    [Functor.IsStronglyCartesian p (p.map a) a]
    {t : 𝒮} {f' : t ⟶ x} {k : t ⟶ z} (hfk : f' ≫ φ = k ≫ g)
    {u : t ⟶ w} (hua : u ≫ a = k)
    (hu : p.map u = Limits.pullback.lift (p.map f') (p.map k)
          (by rw [← Functor.map_comp, ← Functor.map_comp, hfk]) ≫ eqToHom hw.symm) :
    u ≫ b = f' := by
  have h_comp : (u ≫ b) ≫ φ = f' ≫ φ := by
    rw [Category.assoc, hba, ← Category.assoc, hua, hfk]
  have h_map : p.map (u ≫ b) = p.map f' := by
    simp [p.map_comp, hu, hb]
  exact eq_of_map_eq_of_comp_eq p φ h_map h_comp

/-- Given `φ : x ⟶ y` strongly cartesian over `p φ`, an existing fibre product
`p x ×_{p y} p z` in the base, and `a : w ⟶ z` strongly cartesian over the second
projection of that fibre product (as recorded by `hw` and `ha`), there is a morphism
`b : w ⟶ x` lying over the first projection such that the square `(b, a)` is a limit
square, i.e. exhibits `w` as `x ×_y z`. -/
theorem exists_isLimit_pullbackCone_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g))
    [Functor.IsStronglyCartesian p (p.map a) a] :
    ∃ (b : w ⟶ x) (hba : b ≫ φ = a ≫ g),
      p.map b = eqToHom hw ≫ Limits.pullback.fst (p.map φ) (p.map g) ∧
      Nonempty (Limits.IsLimit (Limits.PullbackCone.mk b a hba)) := by
  obtain ⟨b, hba, hbmap⟩ := exists_lift_of_pullbackFst p φ g w a hw ha
  choose u hua hu using fun s : Limits.PullbackCone φ g =>
    exists_lift_of_commSq p φ g w a hw ha s.fst s.snd s.condition
  refine ⟨b, hba, hbmap, ⟨Limits.PullbackCone.IsLimit.mk hba u ?_ hua ?_⟩⟩
  · exact fun s => lift_comp_eq_of_isStronglyCartesian p φ g w a b hw hbmap hba
      s.condition (hua s) (hu s)
  · intro s m hmb hma
    refine eq_of_comp_eq_of_isStronglyCartesian p φ g w a b hw ha hbmap ?_ (by rw [hma, hua])
    rw [hmb]
    exact (lift_comp_eq_of_isStronglyCartesian p φ g w a b hw hbmap hba
      s.condition (hua s) (hu s)).symm

/-- **Stacks 06N4.**
Given `φ : x ⟶ y` strongly cartesian over `p`, an existing fibre product
`p x ×_{p y} p z` in `𝒞`, and a strongly cartesian morphism `a : w ⟶ z` in `𝒮`
lying over the second projection of that fibre product (as recorded by `hw` and `ha`),
the fibre product `x ×_y z` exists in `𝒮`. -/
@[stacks 06N4]
theorem hasPullback_of_isStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g))
    [Functor.IsStronglyCartesian p (p.map a) a] :
    Limits.HasPullback φ g := by
  obtain ⟨b, hba, -, ⟨hlim⟩⟩ :=
    exists_isLimit_pullbackCone_of_isStronglyCartesian p φ g w a hw ha
  exact ⟨⟨⟨_, hlim⟩⟩⟩

/-- **Stacks 06N4.**
In the situation of `hasPullback_of_isStronglyCartesian` the fibre product `x ×_y z`
is canonically isomorphic to `w`: both are limits of the same cospan, `w` by the limit
square built from the strongly cartesian morphisms `φ` and `a`. -/
@[stacks 06N4]
noncomputable def pullbackIsoOfIsStronglyCartesian
    (p : 𝒮 ⥤ 𝒞) {x y z : 𝒮} (φ : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map φ) φ]
    [Limits.HasPullback (p.map φ) (p.map g)]
    (w : 𝒮) (a : w ⟶ z)
    (hw : p.obj w = Limits.pullback (p.map φ) (p.map g))
    (ha : p.map a = eqToHom hw ≫ Limits.pullback.snd (p.map φ) (p.map g))
    [Functor.IsStronglyCartesian p (p.map a) a] [Limits.HasPullback φ g] :
    Limits.pullback φ g ≅ w := by
  choose b hba _hbmap hlim using
    exists_isLimit_pullbackCone_of_isStronglyCartesian p φ g w a hw ha
  exact Limits.IsLimit.conePointUniqueUpToIso (Limits.pullback.isLimit φ g) hlim.some

end CategoryTheory
