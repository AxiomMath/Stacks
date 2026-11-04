module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.MorphismsIntoGluing.GluingReconstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products of schemes in locally ringed spaces

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes. The fibre product `X ×_S Y`, formed in
the category of schemes, is already the fibre product of `f` and `g` in the category of locally
ringed spaces.

## Main results

* `AlgebraicGeometry.Scheme.isPullback_toLRSHom`: the fibre product square of two morphisms of
  schemes is a pullback square of locally ringed spaces.
* `AlgebraicGeometry.LocallyRingedSpace.hasPullback_of_scheme`: the fibre product of two
  morphisms of schemes exists in locally ringed spaces.
* `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace_preservesPullback` and
  `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace_createsPullback`: the forgetful functor
  preserves, indeed creates, fibre products.
* `AlgebraicGeometry.Scheme.isPullback_toLRSHom_of_isAffine`: the case of affine schemes.
* `AlgebraicGeometry.Scheme.jointlyMonoPair_pullback`: a morphism of locally ringed spaces into
  the fibre product is determined by its two projections.
* `AlgebraicGeometry.LocallyRingedSpace.isPullback_of_openCover_left`: being a fibre product of
  locally ringed spaces is local on the upper right corner of the square.

## Implementation notes

The affine case comes from `Spec` being a right adjoint on both sides: both
`AlgebraicGeometry.Scheme.Spec` and `AlgebraicGeometry.Spec.toLocallyRingedSpace` are right
adjoints of the global sections functor, hence preserve all limits, and the two agree after
composing the first with the forgetful functor to locally ringed spaces — the composite is
*equal* to the second, not merely isomorphic. A cospan of spectra is therefore carried to a limit
cone by both, which identifies the scheme-theoretic fibre product of such a cospan with the
locally ringed space one; the general affine case follows by transporting along the canonical
isomorphism of an affine scheme with the spectrum of its global sections.

The general case is reduced to the affine one in three steps, each an instance of
`LocallyRingedSpace.isPullback_of_openCover_left` or its mirror image: cover the base by affine
opens, replace the base by the affine open through which the left leg then factors, and cover the
two sources by affine opens. The covering of a test object used at each step is the inverse image
of the covering of the target under a composite that every morphism in sight shares, which is why
the two halves of the universal property behave differently. Uniqueness of the lift needs only
the extensionality of morphisms of locally ringed spaces over an open covering, so the
`JointlyMonoPair` development below is independent of all gluing; existence needs the gluing of
morphisms, `LocallyRingedSpace.GlueData.existsUnique_hom_of_openCover`, which in turn rests on a
locally ringed space being the gluing of any open covering of itself.

No step of these arguments assumes either leg of the cospan to be an open immersion. Open
immersions enter only as the inclusions of the covering charts and of the affine open of the
base, where they supply the fibre products of locally ringed spaces that Mathlib provides in
that case.

## References

* [Stacks Project, Tag 01JN](https://stacks.math.columbia.edu/tag/01JN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- The forgetful functor from schemes to locally ringed spaces preserves the fibre product of a
cospan of spectra of rings. -/
theorem forgetToLocallyRingedSpace_preservesLimit_cospan_specMap
    {A B C : CommRingCat.{u}} (a : A ⟶ B) (b : A ⟶ C) :
    PreservesLimit (cospan (Spec.map a) (Spec.map b)) forgetToLocallyRingedSpace.{u} := by
  have h₁ : IsLimit (Scheme.Spec.mapCone (limit.cone (cospan a.op b.op))) :=
    isLimitOfPreserves _ (limit.isLimit _)
  have h₂ : IsLimit (Spec.toLocallyRingedSpace.mapCone (limit.cone (cospan a.op b.op))) :=
    isLimitOfPreserves _ (limit.isLimit _)
  have : PreservesLimit (cospan a.op b.op ⋙ Scheme.Spec) forgetToLocallyRingedSpace.{u} :=
    preservesLimit_of_preserves_limit_cone h₁ h₂
  exact preservesLimit_of_iso_diagram _ (cospanCompIso Scheme.Spec a.op b.op)

/-- The forgetful functor from schemes to locally ringed spaces preserves the fibre product of a
cospan of affine schemes. -/
theorem forgetToLocallyRingedSpace_preservesLimit_cospan_of_isAffine
    {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) :
    PreservesLimit (cospan f g) forgetToLocallyRingedSpace.{u} := by
  have := forgetToLocallyRingedSpace_preservesLimit_cospan_specMap f.appTop g.appTop
  have h : ∀ (T : Scheme.{u}) [IsAffine T] (t : T ⟶ S),
      T.isoSpec.symm.hom ≫ t = Spec.map t.appTop ≫ S.isoSpec.symm.hom := by
    intro T _ t
    simp only [Iso.symm_hom]
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoSpec_hom, isoSpec_hom]
    exact toSpecΓ_naturality t
  exact preservesLimit_of_iso_diagram _
    (cospanExt X.isoSpec.symm Y.isoSpec.symm S.isoSpec.symm (h X f) (h Y g))

/-- The fibre product square of a cospan of affine schemes is a pullback square of locally ringed
spaces. -/
theorem isPullback_toLRSHom_of_isAffine {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom := by
  have := forgetToLocallyRingedSpace_preservesLimit_cospan_of_isAffine f g
  exact (IsPullback.of_hasPullback f g).map forgetToLocallyRingedSpace.{u}

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.LocallyRingedSpace

/-- A pair of morphisms out of a locally ringed space is *jointly monic* when a morphism into
their common source is determined by its two composites. -/
def JointlyMonoPair {W X Y : LocallyRingedSpace.{u}} (a : W ⟶ X) (b : W ⟶ Y) : Prop :=
  ∀ ⦃T : LocallyRingedSpace.{u}⦄ (u v : T ⟶ W), u ≫ a = v ≫ a → u ≫ b = v ≫ b → u = v

/-- If `a` and `b` are jointly monic, then so are `b` and `a`. -/
theorem JointlyMonoPair.symm {W X Y : LocallyRingedSpace.{u}} {a : W ⟶ X} {b : W ⟶ Y}
    (h : JointlyMonoPair a b) : JointlyMonoPair b a := by
  exact fun _ u v hu hv => h u v hv hu

/-- The two projections of a pullback square of locally ringed spaces are jointly monic. -/
theorem jointlyMonoPair_of_isPullback {W X Y S : LocallyRingedSpace.{u}} {a : W ⟶ X} {b : W ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (sq : CategoryTheory.IsPullback a b f g) :
    JointlyMonoPair a b :=
  fun _ _ _ hu hv => sq.hom_ext hu hv

/-- Joint monicity transports along an isomorphism of the common source. -/
theorem JointlyMonoPair.of_iso {W W' X Y : LocallyRingedSpace.{u}} (e : W' ≅ W) {a : W ⟶ X}
    {b : W ⟶ Y} {a' : W' ⟶ X} {b' : W' ⟶ Y} (ha : e.hom ≫ a = a') (hb : e.hom ≫ b = b')
    (h : JointlyMonoPair a' b') : JointlyMonoPair a b := by
  subst ha hb
  intro T u v hu hv
  rw [← cancel_mono e.inv]
  refine h (u ≫ e.inv) (v ≫ e.inv) ?_ ?_
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hu
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hv

/-- Joint monicity survives postcomposition of the second leg with a monomorphism. -/
theorem JointlyMonoPair.comp_mono {W X Y Y' : LocallyRingedSpace.{u}} {a : W ⟶ X} {b : W ⟶ Y}
    (h : JointlyMonoPair a b) (n : Y ⟶ Y') [Mono n] : JointlyMonoPair a (b ≫ n) := by
  intro _ u v hu hv
  exact h u v hu ((cancel_mono n).mp (by simpa only [Category.assoc] using hv))

/-- If the `α i` are open immersions covering `X`, their base changes along any `p : T ⟶ X`
cover `T`. -/
private theorem exists_pullback_fst_base_eq {X T : LocallyRingedSpace.{u}} (p : T ⟶ X)
    {ι : Type u} {V : ι → LocallyRingedSpace.{u}} (α : (i : ι) → V i ⟶ X)
    [∀ i, LocallyRingedSpace.IsOpenImmersion (α i)] (hsurj : ∀ x : X, ∃ i y, (α i).base y = x)
    (t : T) : ∃ i z, (pullback.fst p (α i)).base z = t := by
  obtain ⟨i, y, hy⟩ := hsurj (p.base t)
  obtain ⟨z, hz⟩ : t ∈ Set.range (pullback.fst p (α i)).base := by
    rw [GlueData.range_pullback_fst_of_right p (α i)]; exact ⟨y, hy⟩
  exact ⟨i, z, hz⟩

/-- Joint monicity is local on the first target: a pair `(a, b)` is jointly monic as soon as its
base change along each member of an open covering of the first target is. -/
theorem jointlyMonoPair_of_openCover_left {W X Y : LocallyRingedSpace.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    {ι : Type u} {V : ι → LocallyRingedSpace.{u}} (α : (i : ι) → V i ⟶ X)
    [hα : ∀ i, LocallyRingedSpace.IsOpenImmersion (α i)]
    (hsurj : ∀ x : X, ∃ i y, (α i).base y = x)
    (H : ∀ i, JointlyMonoPair (pullback.snd a (α i)) (pullback.fst a (α i) ≫ b)) :
    JointlyMonoPair a b := by
  intro T u v hu hv
  have hrangeσ (i : ι) : Set.range (pullback.fst (u ≫ a) (α i)).base =
      (u ≫ a).base ⁻¹' Set.range (α i).base :=
    GlueData.range_pullback_fst_of_right (u ≫ a) (α i)
  have hrangeπ (i : ι) : Set.range (pullback.fst a (α i)).base =
      a.base ⁻¹' Set.range (α i).base :=
    GlueData.range_pullback_fst_of_right a (α i)
  refine GlueData.hom_ext_of_openCover (fun i => pullback.fst (u ≫ a) (α i))
    (fun i => inferInstance) ?_ u v ?_
  · exact exists_pullback_fst_base_eq (u ≫ a) α hsurj
  · intro i
    have hmem : ∀ z, (u ≫ a).base ((pullback.fst (u ≫ a) (α i)).base z) ∈
        Set.range (α i).base := by
      intro z
      rw [← Set.mem_preimage, ← hrangeσ i]
      exact ⟨z, rfl⟩
    have h₁ : Set.range (pullback.fst (u ≫ a) (α i) ≫ u).base ⊆
        Set.range (pullback.fst a (α i)).base := by
      rw [hrangeπ i]
      rintro _ ⟨z, rfl⟩
      simpa [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply] using hmem z
    have h₂ : Set.range (pullback.fst (u ≫ a) (α i) ≫ v).base ⊆
        Set.range (pullback.fst a (α i)).base := by
      rw [hrangeπ i]
      rintro _ ⟨z, rfl⟩
      have hz := hmem z
      rw [show (u ≫ a).base = (v ≫ a).base from congrArg (fun k : T ⟶ X => k.base) hu] at hz
      simpa [LocallyRingedSpace.comp_base, ConcreteCategory.comp_apply] using hz
    have hfacu := LocallyRingedSpace.IsOpenImmersion.lift_fac (pullback.fst a (α i))
      (pullback.fst (u ≫ a) (α i) ≫ u) h₁
    have hfacv := LocallyRingedSpace.IsOpenImmersion.lift_fac (pullback.fst a (α i))
      (pullback.fst (u ≫ a) (α i) ≫ v) h₂
    have hkey : LocallyRingedSpace.IsOpenImmersion.lift (pullback.fst a (α i))
          (pullback.fst (u ≫ a) (α i) ≫ u) h₁ =
        LocallyRingedSpace.IsOpenImmersion.lift (pullback.fst a (α i))
          (pullback.fst (u ≫ a) (α i) ≫ v) h₂ := by
      refine H i _ _ ?_ ?_
      · rw [← cancel_mono (α i), Category.assoc, Category.assoc, ← pullback.condition,
          ← Category.assoc, ← Category.assoc, hfacu, hfacv, Category.assoc, Category.assoc, hu]
      · rw [← Category.assoc, ← Category.assoc, hfacu, hfacv, Category.assoc, Category.assoc, hv]
    rw [← hfacu, ← hfacv, hkey]

/-- **Local-to-global for fibre products of locally ringed spaces.** A commuting square is a
pullback square as soon as its base change along each member of an open covering of the upper
right corner is. -/
theorem isPullback_of_openCover_left {W X Y S : LocallyRingedSpace.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (hab : a ≫ f = b ≫ g)
    {ι : Type u} {V : ι → LocallyRingedSpace.{u}} (α : (i : ι) → V i ⟶ X)
    [hα : ∀ i, LocallyRingedSpace.IsOpenImmersion (α i)]
    (hsurj : ∀ x : X, ∃ i y, (α i).base y = x)
    (H : ∀ i, CategoryTheory.IsPullback (pullback.snd a (α i))
      (pullback.fst a (α i) ≫ b) (α i ≫ f) g) :
    CategoryTheory.IsPullback a b f g := by
  have hmono : JointlyMonoPair a b :=
    jointlyMonoPair_of_openCover_left a b α hsurj fun i => jointlyMonoPair_of_isPullback (H i)
  have hex : ∀ (T : LocallyRingedSpace.{u}) (p : T ⟶ X) (q : T ⟶ Y), p ≫ f = q ≫ g →
      ∃ h : T ⟶ W, h ≫ a = p ∧ h ≫ b = q := by
    intro T p q hpq
    have hcov := exists_pullback_fst_base_eq p α hsurj
    have hlocal : ∀ i, ∃ k : pullback p (α i) ⟶ W,
        k ≫ a = pullback.fst p (α i) ≫ p ∧ k ≫ b = pullback.fst p (α i) ≫ q := by
      intro i
      have hw : pullback.snd p (α i) ≫ (α i ≫ f) = (pullback.fst p (α i) ≫ q) ≫ g := by
        rw [← Category.assoc, ← pullback.condition, Category.assoc, Category.assoc, hpq]
      refine ⟨(H i).lift (pullback.snd p (α i)) (pullback.fst p (α i) ≫ q) hw ≫
        pullback.fst a (α i), ?_, ?_⟩
      · rw [Category.assoc, pullback.condition, ← Category.assoc,
          (H i).lift_fst, pullback.condition]
      · rw [Category.assoc, (H i).lift_snd]
    choose k hka hkb using hlocal
    obtain ⟨h, hh, -⟩ := GlueData.existsUnique_hom_of_openCover
      (fun i => pullback.fst p (α i)) hcov k (by
        intro i j
        refine hmono _ _ ?_ ?_
        · rw [Category.assoc, Category.assoc, hka, hka, ← Category.assoc, ← Category.assoc,
            pullback.condition]
        · rw [Category.assoc, Category.assoc, hkb, hkb, ← Category.assoc, ← Category.assoc,
            pullback.condition])
    refine ⟨h, ?_, ?_⟩
    · refine GlueData.hom_ext_of_openCover (fun i => pullback.fst p (α i))
        (fun i => inferInstance) hcov _ _ fun i => ?_
      rw [← Category.assoc, hh i, hka i]
    · refine GlueData.hom_ext_of_openCover (fun i => pullback.fst p (α i))
        (fun i => inferInstance) hcov _ _ fun i => ?_
      rw [← Category.assoc, hh i, hkb i]
  exact CategoryTheory.IsPullback.of_isLimit (PullbackCone.IsLimit.mk hab
    (fun s => Classical.choose (hex s.pt s.fst s.snd s.condition))
    (fun s => (Classical.choose_spec (hex s.pt s.fst s.snd s.condition)).1)
    (fun s => (Classical.choose_spec (hex s.pt s.fst s.snd s.condition)).2)
    (fun s m h₁ h₂ => hmono _ _
      (h₁.trans (Classical.choose_spec (hex s.pt s.fst s.snd s.condition)).1.symm)
      (h₂.trans (Classical.choose_spec (hex s.pt s.fst s.snd s.condition)).2.symm)))

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Scheme

/-- The base changes of a morphism `f : X ⟶ S` along the charts of an affine cover of `S` cover
`X`. -/
private theorem exists_pullback_fst_affineCover_base_eq {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    ∃ l y, (pullback.fst f (S.affineCover.f l)).base y = x := by
  obtain ⟨l, y, hy⟩ := S.affineCover.exists_eq (f.base x)
  obtain ⟨z, hz⟩ : x ∈ Set.range (pullback.fst f (S.affineCover.f l)).base := by
    rw [AlgebraicGeometry.IsOpenImmersion.range_pullbackFst]
    exact ⟨y, hy⟩
  exact ⟨l, z, hz⟩

/-- Being a pullback square transports along an isomorphism of the upper left corner. -/
private theorem isPullback_of_iso_hom_comp_eq {C : Type*} [Category C] {W W' X Y S : C}
    (e : W ≅ W') {a : W ⟶ X} {b : W ⟶ Y} {a' : W' ⟶ X} {b' : W' ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (ha : e.hom ≫ a' = a) (hb : e.hom ≫ b' = b) (h : IsPullback a b f g) :
    IsPullback a' b' f g :=
  h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa using ha.symm)
    (by simpa using hb.symm) (by simp) (by simp)

open AlgebraicGeometry.LocallyRingedSpace in
/-- Joint monicity of the two projections of a fibre product of schemes, tested against locally
ringed spaces, is local on the source of the left leg: it is enough to know it for the cospans
obtained by restricting the left leg to the members of an open covering of its source. -/
theorem jointlyMonoPair_pullback_of_cover_left {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {ι : Type u} {U : ι → Scheme.{u}} (𝒻 : (i : ι) → U i ⟶ X)
    (hoi : ∀ i, AlgebraicGeometry.IsOpenImmersion (𝒻 i))
    (hcov : ∀ x : X, ∃ i y, (𝒻 i).base y = x)
    (H : ∀ i, JointlyMonoPair (pullback.fst (𝒻 i ≫ f) g).toLRSHom
      (pullback.snd (𝒻 i ≫ f) g).toLRSHom) :
    JointlyMonoPair (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom := by
  have hoiL : ∀ i, LocallyRingedSpace.IsOpenImmersion (𝒻 i).toLRSHom := fun i =>
    have := hoi i; inferInstance
  refine jointlyMonoPair_of_openCover_left (hα := hoiL) (pullback.fst f g).toLRSHom
    (pullback.snd f g).toLRSHom (fun i => (𝒻 i).toLRSHom) ?_ ?_
  · exact hcov
  · intro i
    have := hoi i
    have := hoiL i
    have sqS := IsPullback.of_hasPullback (𝒻 i) (pullback.fst f g)
    have sq₁ := IsPullback.of_hasPullback (𝒻 i ≫ f) g
    have sq₂ := sqS.paste_vert (IsPullback.of_hasPullback f g)
    have key : JointlyMonoPair (pullback.fst (𝒻 i) (pullback.fst f g)).toLRSHom
        (pullback.snd (𝒻 i) (pullback.fst f g) ≫ pullback.snd f g).toLRSHom :=
      JointlyMonoPair.of_iso
        (forgetToLocallyRingedSpace.{u}.mapIso (sq₁.isoIsPullback _ _ sq₂))
        (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_fst _ _ sq₁ sq₂))
        (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_snd _ _ sq₁ sq₂)) (H i)
    have sq₃ : IsPullback (pullback.snd (𝒻 i) (pullback.fst f g)).toLRSHom
        (pullback.fst (𝒻 i) (pullback.fst f g)).toLRSHom
        (pullback.fst f g).toLRSHom (𝒻 i).toLRSHom :=
      (sqS.map forgetToLocallyRingedSpace.{u}).flip
    have sq₄ := IsPullback.of_hasPullback (pullback.fst f g).toLRSHom (𝒻 i).toLRSHom
    refine JointlyMonoPair.of_iso (sq₃.isoIsPullback _ _ sq₄)
      (IsPullback.isoIsPullback_hom_snd _ _ sq₃ sq₄) ?_ key
    rw [← Category.assoc, IsPullback.isoIsPullback_hom_fst _ _ sq₃ sq₄]
    rfl

open AlgebraicGeometry.LocallyRingedSpace in
/-- The projections of `X ×_S Y` are jointly monic in locally ringed spaces if those of
`Y ×_S X` are. -/
theorem jointlyMonoPair_pullback_symm {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : JointlyMonoPair (pullback.fst g f).toLRSHom (pullback.snd g f).toLRSHom) :
    JointlyMonoPair (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom :=
  JointlyMonoPair.of_iso (forgetToLocallyRingedSpace.{u}.mapIso (pullbackSymmetry g f))
    (congrArg Scheme.Hom.toLRSHom (pullbackSymmetry_hom_comp_fst g f))
    (congrArg Scheme.Hom.toLRSHom (pullbackSymmetry_hom_comp_snd g f)) h.symm

open AlgebraicGeometry.LocallyRingedSpace in
/-- The mirror image of `jointlyMonoPair_pullback_of_cover_left`: joint monicity is equally local
on the source of the right leg. -/
theorem jointlyMonoPair_pullback_of_cover_right {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {ι : Type u} {V : ι → Scheme.{u}} (ℊ : (i : ι) → V i ⟶ Y)
    (hoi : ∀ i, AlgebraicGeometry.IsOpenImmersion (ℊ i))
    (hcov : ∀ y : Y, ∃ i z, (ℊ i).base z = y)
    (H : ∀ i, JointlyMonoPair (pullback.fst f (ℊ i ≫ g)).toLRSHom
      (pullback.snd f (ℊ i ≫ g)).toLRSHom) :
    JointlyMonoPair (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom :=
  jointlyMonoPair_pullback_symm f g
    (jointlyMonoPair_pullback_of_cover_left g f ℊ hoi hcov fun i =>
      jointlyMonoPair_pullback_symm (ℊ i ≫ g) f (H i))

open AlgebraicGeometry.LocallyRingedSpace in
/-- The base may be replaced by an open subscheme through which the left leg factors: the fibre
product is unchanged when the right leg is restricted to the inverse image of that subscheme. -/
theorem jointlyMonoPair_pullback_of_factorsThroughOpen {X Y S S' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (m : S' ⟶ S) [AlgebraicGeometry.IsOpenImmersion m] (f' : X ⟶ S')
    (hf : f' ≫ m = f)
    (H : JointlyMonoPair (pullback.fst f' (pullback.snd g m)).toLRSHom
      (pullback.snd f' (pullback.snd g m)).toLRSHom) :
    JointlyMonoPair (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom := by
  subst hf
  have hn : AlgebraicGeometry.IsOpenImmersion (pullback.fst g m) := inferInstance
  have hnL : LocallyRingedSpace.IsOpenImmersion (pullback.fst g m).toLRSHom := inferInstance
  have sqP := (IsPullback.of_hasPullback f' (pullback.snd g m)).paste_vert
    (IsPullback.of_hasPullback g m).flip
  have sq₃ := IsPullback.of_hasPullback (f' ≫ m) g
  exact JointlyMonoPair.of_iso
    (forgetToLocallyRingedSpace.{u}.mapIso (sqP.isoIsPullback _ _ sq₃))
    (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_fst _ _ sqP sq₃))
    (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_snd _ _ sqP sq₃))
    (H.comp_mono (pullback.fst g m).toLRSHom)

open AlgebraicGeometry.LocallyRingedSpace in
/-- A morphism of locally ringed spaces into the fibre product of two morphisms of schemes is
determined by its two projections. Neither leg of the cospan is assumed to be an open
immersion. -/
theorem jointlyMonoPair_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    JointlyMonoPair (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom := by
  refine jointlyMonoPair_pullback_of_cover_left f g
    (fun l => pullback.fst f (S.affineCover.f l)) (fun l => inferInstance) ?_ ?_
  · exact exists_pullback_fst_affineCover_base_eq f
  · intro l
    refine jointlyMonoPair_pullback_of_factorsThroughOpen _ g (S.affineCover.f l)
      (pullback.snd f (S.affineCover.f l)) pullback.condition.symm ?_
    refine jointlyMonoPair_pullback_of_cover_left _ _
      (fun j => (pullback f (S.affineCover.f l)).affineCover.f j) (fun j => inferInstance)
      (fun x => (pullback f (S.affineCover.f l)).affineCover.exists_eq x) ?_
    intro j
    refine jointlyMonoPair_pullback_of_cover_right _ _
      (fun k => (pullback g (S.affineCover.f l)).affineCover.f k) (fun k => inferInstance)
      (fun y => (pullback g (S.affineCover.f l)).affineCover.exists_eq y) ?_
    intro k
    exact LocallyRingedSpace.jointlyMonoPair_of_isPullback
      (isPullback_toLRSHom_of_isAffine _ _)

/-- The fibre product square of schemes, read in locally ringed spaces, is a pullback square as
soon as it is so after restricting the left leg to the members of an open covering of its
source. -/
theorem isPullback_toLRSHom_of_cover_left {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {ι : Type u} {U : ι → Scheme.{u}} (𝒻 : (i : ι) → U i ⟶ X)
    (hoi : ∀ i, AlgebraicGeometry.IsOpenImmersion (𝒻 i))
    (hcov : ∀ x : X, ∃ i y, (𝒻 i).base y = x)
    (H : ∀ i, IsPullback (pullback.fst (𝒻 i ≫ f) g).toLRSHom
      (pullback.snd (𝒻 i ≫ f) g).toLRSHom (𝒻 i ≫ f).toLRSHom g.toLRSHom) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom := by
  have hoiL : ∀ i, LocallyRingedSpace.IsOpenImmersion (𝒻 i).toLRSHom := fun i =>
    have := hoi i; inferInstance
  refine LocallyRingedSpace.isPullback_of_openCover_left (hα := hoiL)
    (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom
    (by rw [← Hom.comp_toLRSHom, ← Hom.comp_toLRSHom, pullback.condition])
    (fun i => (𝒻 i).toLRSHom) ?_ ?_
  · exact hcov
  · intro i
    have := hoi i
    have := hoiL i
    have Hi : IsPullback (pullback.fst (𝒻 i ≫ f) g).toLRSHom
        (pullback.snd (𝒻 i ≫ f) g).toLRSHom ((𝒻 i).toLRSHom ≫ f.toLRSHom) g.toLRSHom := H i
    have sqS := IsPullback.of_hasPullback (𝒻 i) (pullback.fst f g)
    have sq₁ := IsPullback.of_hasPullback (𝒻 i ≫ f) g
    have sq₂ := sqS.paste_vert (IsPullback.of_hasPullback f g)
    have sq₃ : IsPullback (pullback.snd (𝒻 i) (pullback.fst f g)).toLRSHom
        (pullback.fst (𝒻 i) (pullback.fst f g)).toLRSHom
        (pullback.fst f g).toLRSHom (𝒻 i).toLRSHom :=
      (sqS.map forgetToLocallyRingedSpace.{u}).flip
    have sq₄ := IsPullback.of_hasPullback (pullback.fst f g).toLRSHom (𝒻 i).toLRSHom
    have stepA : IsPullback (pullback.fst (𝒻 i) (pullback.fst f g)).toLRSHom
        ((pullback.snd (𝒻 i) (pullback.fst f g)).toLRSHom ≫ (pullback.snd f g).toLRSHom)
        ((𝒻 i).toLRSHom ≫ f.toLRSHom) g.toLRSHom := by
      exact isPullback_of_iso_hom_comp_eq
        (forgetToLocallyRingedSpace.{u}.mapIso (sq₁.isoIsPullback _ _ sq₂))
        (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_fst _ _ sq₁ sq₂))
        (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_snd _ _ sq₁ sq₂)) Hi
    refine isPullback_of_iso_hom_comp_eq (sq₃.isoIsPullback _ _ sq₄)
      (IsPullback.isoIsPullback_hom_snd _ _ sq₃ sq₄) ?_ stepA
    rw [← Category.assoc, IsPullback.isoIsPullback_hom_fst _ _ sq₃ sq₄]

/-- The fibre product square of `X ×_S Y` is a pullback square of locally ringed spaces if that of
`Y ×_S X` is. -/
theorem isPullback_toLRSHom_symm {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (h : IsPullback (pullback.fst g f).toLRSHom (pullback.snd g f).toLRSHom
      g.toLRSHom f.toLRSHom) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom := by
  exact isPullback_of_iso_hom_comp_eq (forgetToLocallyRingedSpace.{u}.mapIso (pullbackSymmetry g f))
    (congrArg Scheme.Hom.toLRSHom (pullbackSymmetry_hom_comp_fst g f))
    (congrArg Scheme.Hom.toLRSHom (pullbackSymmetry_hom_comp_snd g f)) h.flip

/-- The mirror image of `isPullback_toLRSHom_of_cover_left`. -/
theorem isPullback_toLRSHom_of_cover_right {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    {ι : Type u} {V : ι → Scheme.{u}} (ℊ : (i : ι) → V i ⟶ Y)
    (hoi : ∀ i, AlgebraicGeometry.IsOpenImmersion (ℊ i))
    (hcov : ∀ y : Y, ∃ i z, (ℊ i).base z = y)
    (H : ∀ i, IsPullback (pullback.fst f (ℊ i ≫ g)).toLRSHom
      (pullback.snd f (ℊ i ≫ g)).toLRSHom f.toLRSHom (ℊ i ≫ g).toLRSHom) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom :=
  isPullback_toLRSHom_symm f g
    (isPullback_toLRSHom_of_cover_left g f ℊ hoi hcov fun i =>
      isPullback_toLRSHom_symm (ℊ i ≫ g) f (H i))

/-- The base may be replaced by an open subscheme through which the left leg factors: the fibre
product is unchanged when the right leg is restricted to the inverse image of that subscheme. -/
theorem isPullback_toLRSHom_of_factorsThroughOpen {X Y S S' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (m : S' ⟶ S) [AlgebraicGeometry.IsOpenImmersion m] (f' : X ⟶ S')
    (hf : f' ≫ m = f)
    (H : IsPullback (pullback.fst f' (pullback.snd g m)).toLRSHom
      (pullback.snd f' (pullback.snd g m)).toLRSHom f'.toLRSHom (pullback.snd g m).toLRSHom) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom := by
  subst hf
  have hnL : LocallyRingedSpace.IsOpenImmersion (pullback.fst g m).toLRSHom := inferInstance
  have hmL : LocallyRingedSpace.IsOpenImmersion m.toLRSHom := inferInstance
  have sqL : IsPullback (pullback.snd g m).toLRSHom (pullback.fst g m).toLRSHom
      m.toLRSHom g.toLRSHom :=
    ((IsPullback.of_hasPullback g m).map forgetToLocallyRingedSpace.{u}).flip
  have sqP : IsPullback (pullback.fst f' (pullback.snd g m)).toLRSHom
      ((pullback.snd f' (pullback.snd g m)).toLRSHom ≫ (pullback.fst g m).toLRSHom)
      (f' ≫ m).toLRSHom g.toLRSHom :=
    H.paste_vert sqL
  have sqPS := (IsPullback.of_hasPullback f' (pullback.snd g m)).paste_vert
    (IsPullback.of_hasPullback g m).flip
  have sqQ := IsPullback.of_hasPullback (f' ≫ m) g
  exact isPullback_of_iso_hom_comp_eq
    (forgetToLocallyRingedSpace.{u}.mapIso (sqPS.isoIsPullback _ _ sqQ))
    (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_fst _ _ sqPS sqQ))
    (congrArg Scheme.Hom.toLRSHom (IsPullback.isoIsPullback_hom_snd _ _ sqPS sqQ)) sqP

/-- The fibre product of two morphisms of schemes, formed in `Scheme`, is already the fibre
product in locally ringed spaces. Neither leg of the cospan is assumed to be
an open immersion. -/
@[stacks 01JN]
theorem isPullback_toLRSHom {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    IsPullback (pullback.fst f g).toLRSHom (pullback.snd f g).toLRSHom f.toLRSHom g.toLRSHom := by
  refine isPullback_toLRSHom_of_cover_left f g
    (fun l => pullback.fst f (S.affineCover.f l)) (fun l => inferInstance) ?_ ?_
  · exact exists_pullback_fst_affineCover_base_eq f
  · intro l
    refine isPullback_toLRSHom_of_factorsThroughOpen _ g (S.affineCover.f l)
      (pullback.snd f (S.affineCover.f l)) pullback.condition.symm ?_
    refine isPullback_toLRSHom_of_cover_left _ _
      (fun j => (pullback f (S.affineCover.f l)).affineCover.f j) (fun j => inferInstance)
      (fun x => (pullback f (S.affineCover.f l)).affineCover.exists_eq x) ?_
    intro j
    refine isPullback_toLRSHom_of_cover_right _ _
      (fun k => (pullback g (S.affineCover.f l)).affineCover.f k) (fun k => inferInstance)
      (fun y => (pullback g (S.affineCover.f l)).affineCover.exists_eq y) ?_
    intro k
    exact isPullback_toLRSHom_of_isAffine _ _

/-- The forgetful functor from schemes to locally ringed spaces preserves fibre products. -/
instance forgetToLocallyRingedSpace_preservesPullback {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) :
    PreservesLimit (cospan f g) forgetToLocallyRingedSpace.{u} :=
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv forgetToLocallyRingedSpace.{u}
      (IsPullback.of_hasPullback f g).w).symm (isPullback_toLRSHom f g).isLimit)

/-- The forgetful functor from schemes to locally ringed spaces creates fibre products: a fibre
product of two morphisms of schemes taken in locally ringed spaces is a scheme. -/
noncomputable instance forgetToLocallyRingedSpace_createsPullback {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) :
    CreatesLimit (cospan f g) forgetToLocallyRingedSpace.{u} :=
  @createsLimitOfFullyFaithfulOfPreserves _ _ _ _ _ _ (cospan f g)
    forgetToLocallyRingedSpace.{u} _ _ _ (forgetToLocallyRingedSpace_preservesPullback f g)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The fibre product of two morphisms of schemes exists in the category of locally ringed
spaces. -/
@[stacks 01JN]
instance hasPullback_of_scheme {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    HasPullback f.toLRSHom g.toLRSHom :=
  (Scheme.isPullback_toLRSHom f g).hasPullback

end AlgebraicGeometry.LocallyRingedSpace

end
