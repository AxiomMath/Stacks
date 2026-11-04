module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.RingTheory.Smooth.Lifting
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms into an étale scheme over a topologically unchanged closed subscheme

Let `i : S₀ ⟶ S` be a closed immersion which is surjective on points, i.e. a thickening.
If `X` is étale over `S`, then base change along `i` is a bijection from the `S`-morphisms
`Y ⟶ X` to the `S₀`-morphisms between the base changes.

## Main results

* `Stacks.Etale.hom_ext_of_surjective`: two morphisms into a scheme étale over `S` which agree
  over `S` and agree after precomposition with a morphism that is surjective on points are
  equal.
* `Stacks.Etale.exists_lift_of_surjective_closedImmersion`: an `S`-morphism out of a
  topologically unchanged closed subscheme of `Y` into a scheme étale over `S` extends to `Y`.
* `Stacks.Etale.bijective_pullbackHom_of_etale`: base change along a closed immersion with the
  same underlying space induces a bijection on morphisms into an étale scheme.

## Implementation notes

The equality of underlying topological spaces is expressed by surjectivity of the closed
immersion on points. Objects of `Over S` encode schemes over `S`, and `Over.pullback` is the
canonical base-change functor.

The affine case is the lifting property of smooth algebras along a locally nilpotent ideal,
`main_theorem07K4`: a closed immersion of affine schemes which is surjective on points is cut
out by a locally nilpotent ideal. The general case is obtained by choosing, around each point
of `Y`, affine charts in which the lift exists, and glueing the local lifts; the glueing data
is compatible because of `hom_ext_of_surjective`, which is also what makes the lift unique.

## References

* [Stacks Project, Tag 025H](https://stacks.math.columbia.edu/tag/025H)
-/

@[expose] public section

namespace Stacks.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- Lifting an algebra map along a surjection with locally nilpotent kernel, out of a smooth
algebra. This is `main_theorem07K4` phrased for a surjection of algebras rather than for a
quotient by an ideal. -/
private lemma exists_algHom_lift_of_surjective_of_isLocallyNilpotent
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra.Smooth R B]
    (j : A →ₐ[R] C) (hj : Function.Surjective j)
    (hI : Ideal.IsLocallyNilpotent (RingHom.ker j.toRingHom))
    (g : B →ₐ[R] C) :
    ∃ f : B →ₐ[R] A, j.comp f = g := by
  let e := Ideal.quotientKerAlgEquivOfSurjective hj
  obtain ⟨f, hf⟩ := main_theorem07K4 R B A (RingHom.ker j.toRingHom) hI
    (e.symm.toAlgHom.comp g)
  refine ⟨f, AlgHom.ext fun b => ?_⟩
  have hb := AlgHom.congr_fun hf b
  change Ideal.Quotient.mk (RingHom.ker j) (f b) = e.symm (g b) at hb
  change e (Ideal.Quotient.mk (RingHom.ker j) (f b)) = g b
  rw [hb, AlgEquiv.apply_symm_apply]

/-- A closed immersion into an affine scheme which is surjective on points is cut out by a
locally nilpotent ideal. -/
private lemma isLocallyNilpotent_ker_of_surjective
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (hf : Function.Surjective f.base) :
    Ideal.IsLocallyNilpotent (RingHom.ker f.appTop.hom) := by
  have hsupport : (f.ker.support : Set Y) = Set.univ := by
    rw [Scheme.Hom.support_ker, Set.range_eq_univ.mpr hf, closure_univ]
  rw [Scheme.ker_of_isAffine f] at hsupport
  have hker : (RingHom.ker f.appTop.hom : Set Γ(Y, ⊤)) ⊆ nilradical Γ(Y, ⊤) := by
    rw [← Scheme.zeroLocus_eq_univ_iff_subset_nilradical]
    simpa using hsupport
  exact fun a ha => mem_nilradical.mp (hker ha)

/-- The affine case of the lifting property: a morphism out of a topologically unchanged closed
subscheme `Z` of an affine scheme `U`, into a scheme `W` étale over an affine base `T`, extends
to `U` compatibly with the structure morphisms. -/
private lemma exists_lift_of_isAffine
    {Z U W T : Scheme.{u}} [IsAffine U] [IsAffine W] [IsAffine T]
    (i : Z ⟶ U) [IsClosedImmersion i] (hi : Function.Surjective i.base)
    (p : U ⟶ T) (q : W ⟶ T) [Etale q] (g : Z ⟶ W) (hg : i ≫ p = g ≫ q) :
    ∃ f : U ⟶ W, i ≫ f = g ∧ f ≫ q = p := by
  classical
  let R := Γ(T, ⊤)
  let A := Γ(U, ⊤)
  let B := Γ(W, ⊤)
  let φ : R →+* A := p.appTop.hom
  let ψ : R →+* B := q.appTop.hom
  let ι : A →+* Γ(Z, ⊤) := i.appTop.hom
  let κ : B →+* Γ(Z, ⊤) := g.appTop.hom
  have hring : ι.comp φ = κ.comp ψ := by
    have h := congrArg Scheme.Hom.appTop hg
    simp only [Scheme.Hom.comp_appTop] at h
    exact congrArg CommRingCat.Hom.hom h
  let : Algebra R A := φ.toAlgebra
  let : Algebra R B := ψ.toAlgebra
  let : Algebra A Γ(Z, ⊤) := ι.toAlgebra
  let : Algebra R Γ(Z, ⊤) := (ι.comp φ).toAlgebra
  have : IsScalarTower R A Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  let ji : A →ₐ[R] Γ(Z, ⊤) := { toRingHom := ι, commutes' := fun _ => rfl }
  let gi : B →ₐ[R] Γ(Z, ⊤) :=
    { toRingHom := κ
      commutes' := fun r => (RingHom.congr_fun hring r).symm }
  have hji : Function.Surjective ji := by
    simpa [ji, ι] using (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hnil : Ideal.IsLocallyNilpotent (RingHom.ker ji.toRingHom) := by
    simpa [ji, ι] using isLocallyNilpotent_ker_of_surjective i hi
  have : Algebra.Etale R B := RingHom.etale_algebraMap.mpr <|
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹Etale q›
  obtain ⟨lift, hlift⟩ :=
    exists_algHom_lift_of_surjective_of_isLocallyNilpotent ji hji hnil gi
  let f : U ⟶ W :=
    U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lift.toRingHom) ≫ W.isoSpec.inv
  have hf : f.appTop.hom = lift.toRingHom := by
    have hmap : Spec.map f.appTop = Spec.map (CommRingCat.ofHom lift.toRingHom) := by
      apply (cancel_mono W.isoSpec.inv).1
      rw [Scheme.isoSpec_inv_naturality]
      simp [f]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective hmap)
  refine ⟨f, ?_, ?_⟩
  · refine ext_of_isAffine (CommRingCat.hom_ext ?_)
    change i.appTop.hom.comp f.appTop.hom = g.appTop.hom
    rw [hf]
    exact congrArg AlgHom.toRingHom hlift
  · refine ext_of_isAffine (CommRingCat.hom_ext ?_)
    change f.appTop.hom.comp q.appTop.hom = p.appTop.hom
    rw [hf]
    ext r
    exact lift.commutes r

/-- The local case of the lifting property: given affine charts `U ⊆ Y`, `T ⊆ S` and `W ⊆ X`
with `U` mapping into `T`, `W` mapping into `T`, and the part of `Z` above `U` mapping into
`W`, the morphism `g` extends over `U`. -/
private lemma exists_lift_on_affine_opens
    {S X Y Z : Scheme.{u}} (p : X ⟶ S) [Etale p] (q : Y ⟶ S)
    (j : Z ⟶ Y) [IsClosedImmersion j] (hj : Function.Surjective j.base)
    (g : Z ⟶ X) (hg : j ≫ q = g ≫ p)
    (U : Y.Opens) (hUaff : IsAffineOpen U) (T : S.Opens) (hTaff : IsAffineOpen T)
    (W : X.Opens) (hWaff : IsAffineOpen W) (hU : U ≤ q ⁻¹ᵁ T) (hW : W ≤ p ⁻¹ᵁ T)
    (hGW : ∀ z, j.base z ∈ U → g.base z ∈ W) :
    ∃ f : U.toScheme ⟶ X,
      U.ι ≫ q = f ≫ p ∧ pullback.fst U.ι j ≫ f = pullback.snd U.ι j ≫ g := by
  classical
  let u := U.ι
  let v := T.ι
  let w := W.ι
  let a : pullback u j ⟶ U.toScheme := pullback.fst u j
  let b : pullback u j ⟶ Z := pullback.snd u j
  have : IsClosedImmersion a := inferInstance
  have : Surjective j := ⟨hj⟩
  have : Surjective a := inferInstance
  have : IsAffine U.toScheme := hUaff
  have : IsAffine T.toScheme := hTaff
  have : IsAffine W.toScheme := hWaff
  have hqRange : Set.range (u ≫ q).base ⊆ Set.range v.base := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨q.base (u.base x), hU x.2⟩, rfl⟩
  have hpRange : Set.range (w ≫ p).base ⊆ Set.range v.base := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨p.base (w.base x), hW x.2⟩, rfl⟩
  let r : U.toScheme ⟶ T.toScheme := IsOpenImmersion.lift v (u ≫ q) hqRange
  let s : W.toScheme ⟶ T.toScheme := IsOpenImmersion.lift v (w ≫ p) hpRange
  have : Etale s := by
    have : Etale (s ≫ v) := by simpa [s] using (inferInstance : Etale (w ≫ p))
    exact Etale.of_comp (f := s) v
  have hgRange : Set.range (b ≫ g).base ⊆ Set.range w.base := by
    rintro x ⟨z, rfl⟩
    refine ⟨⟨g.base (b.base z), ?_⟩, rfl⟩
    have hz : u.base (a.base z) = j.base (b.base z) :=
      congrArg (fun f : pullback u j ⟶ Y => f.base z) (pullback.condition (f := u) (g := j))
    exact hGW _ (by rw [← hz]; exact (a.base z).2)
  let gW : pullback u j ⟶ W.toScheme := IsOpenImmersion.lift w (b ≫ g) hgRange
  have hcomm : a ≫ r = gW ≫ s := by
    apply (cancel_mono v).1
    calc
      (a ≫ r) ≫ v = a ≫ u ≫ q := by simp [r]
      _ = b ≫ j ≫ q := pullback.condition_assoc q
      _ = b ≫ g ≫ p := by rw [hg]
      _ = (gW ≫ s) ≫ v := by simp [s, gW]
  obtain ⟨f, hfi, hfp⟩ :=
    exists_lift_of_isAffine a (Surjective.surj (f := a)) r s gW hcomm
  refine ⟨f ≫ w, ?_, ?_⟩
  · calc
      u ≫ q = r ≫ v := (IsOpenImmersion.lift_fac v (u ≫ q) hqRange).symm
      _ = (f ≫ s) ≫ v := by rw [hfp]
      _ = (f ≫ w) ≫ p := by simp [s]
  · rw [reassoc_of% hfi]
    exact IsOpenImmersion.lift_fac w (b ≫ g) hgRange

/-- Around every point of `Y` there is an open on which the lift of `g` exists. -/
private lemma exists_lift_nbhd
    {S X Y Z : Scheme.{u}} (p : X ⟶ S) [Etale p] (q : Y ⟶ S)
    (j : Z ⟶ Y) [IsClosedImmersion j] (hj : Function.Surjective j.base)
    (g : Z ⟶ X) (hg : j ≫ q = g ≫ p) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ f : U.toScheme ⟶ X,
      U.ι ≫ q = f ≫ p ∧ pullback.fst U.ι j ≫ f = pullback.snd U.ι j ≫ g := by
  classical
  obtain ⟨z, hz⟩ := hj y
  obtain ⟨_, ⟨T, hTaff, rfl⟩, hyT, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (q.base y)) isOpen_univ
  have hxT : p.base (g.base z) ∈ T := by
    have h := congrArg (fun k : Z ⟶ S => k.base z) hg
    change q.base (j.base z) = p.base (g.base z) at h
    rw [hz] at h
    simpa [h] using hyT
  obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxT (T.2.preimage p.continuous)
  let e := j.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hj
  let O₀ : Z.Opens := (g ⁻¹ᵁ W) ⊓ ((j ≫ q) ⁻¹ᵁ T)
  have hz₀ : z ∈ O₀ := ⟨hxW, by simpa [hz] using hyT⟩
  let O : Y.Opens := ⟨e '' (O₀ : Set Z), e.isOpenMap (O₀ : Set Z) O₀.2⟩
  have hyO : y ∈ O := ⟨z, hz₀, by simpa [e] using hz⟩
  obtain ⟨_, ⟨U, hUaff, rfl⟩, hyU, hUle⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyO O.2
  have hU : U ≤ q ⁻¹ᵁ T := by
    intro y' hy'
    obtain ⟨z', hz'O, hz'e⟩ := hUle hy'
    have hz' : j.base z' = y' := by simpa [e] using hz'e
    change q.base y' ∈ T
    rw [← hz']
    exact hz'O.2
  have hGW : ∀ z', j.base z' ∈ U → g.base z' ∈ W := by
    intro z' hz'
    obtain ⟨z'', hz''O, hz''e⟩ := hUle hz'
    have : z'' = z' := e.injective (by simpa [e] using hz''e)
    simpa [this] using hz''O.1
  exact ⟨U, hyU, exists_lift_on_affine_opens p q j hj g hg U hUaff T hTaff W hWaff hU hWle hGW⟩

/-- Two morphisms into a scheme étale over `S`, which agree as morphisms over `S` and agree
after precomposition with a morphism that is surjective on points, are equal.

This is the uniqueness half of the topological invariance of the small étale site: no closed
immersion hypothesis is needed, only surjectivity. -/
theorem hom_ext_of_surjective
    {S X Y Z : Scheme.{u}} (j : Z ⟶ Y) (hj : Function.Surjective j.base)
    (p : X ⟶ S) [Etale p] (f g : Y ⟶ X) (hfg : f ≫ p = g ≫ p) (h : j ≫ f = j ≫ g) :
    f = g := by
  let δ : X ⟶ pullback p p := pullback.diagonal p
  let k : Y ⟶ pullback p p := pullback.lift f g hfg
  have hjk : j ≫ k = (j ≫ f) ≫ δ := by
    apply pullback.hom_ext
    · simp [Category.assoc, k, δ, pullback.lift_fst, pullback.diagonal_fst]
    · simp [Category.assoc, k, δ, h, pullback.lift_snd, pullback.diagonal_snd]
  have hkRange : Set.range k ⊆ Set.range δ := by
    rintro z ⟨y, rfl⟩
    obtain ⟨y₀, hy₀⟩ := hj y
    have hpoint : k.base (j.base y₀) = δ.base ((j ≫ f).base y₀) :=
      congrArg (fun q : Z ⟶ pullback p p => q.base y₀) hjk
    exact ⟨(j ≫ f).base y₀, by simpa [hy₀] using hpoint.symm⟩
  let l : Y ⟶ X := IsOpenImmersion.lift δ k hkRange
  have hkd : k = l ≫ δ := (IsOpenImmersion.lift_fac δ k hkRange).symm
  calc
    f = k ≫ pullback.fst p p := (pullback.lift_fst f g hfg).symm
    _ = l := by simp [hkd, δ]
    _ = k ≫ pullback.snd p p := by simp [hkd, δ]
    _ = g := pullback.lift_snd f g hfg

/-- Two local lifts of `g`, defined on `A` and `B` over `Y`, agree on `A ×_Y B`. -/
private lemma lift_eq_on_pullback
    {S X Y Z A B : Scheme.{u}} (p : X ⟶ S) [Etale p] (q : Y ⟶ S)
    (j : Z ⟶ Y) (hj : Function.Surjective j.base) (g : Z ⟶ X)
    (a : A ⟶ Y) (b : B ⟶ Y) (Fa : A ⟶ X) (Fb : B ⟶ X)
    (ha : a ≫ q = Fa ≫ p) (hb : b ≫ q = Fb ≫ p)
    (haj : pullback.fst a j ≫ Fa = pullback.snd a j ≫ g)
    (hbj : pullback.fst b j ≫ Fb = pullback.snd b j ≫ g) :
    pullback.fst a b ≫ Fa = pullback.snd a b ≫ Fb := by
  let d := pullback.fst a b
  let e := pullback.snd a b
  let r : pullback a b ⟶ Y := d ≫ a
  let t := pullback.fst r j
  let z := pullback.snd r j
  have hde : d ≫ a = e ≫ b := pullback.condition
  have hcond_i : t ≫ (d ≫ a) = z ≫ j := pullback.condition
  have hcond_k : t ≫ (e ≫ b) = z ≫ j := by rwa [← hde]
  have : Surjective j := ⟨hj⟩
  let mi : pullback r j ⟶ pullback a j :=
    pullback.lift (t ≫ d) z (by simpa [Category.assoc] using hcond_i)
  let mk : pullback r j ⟶ pullback b j :=
    pullback.lift (t ≫ e) z (by simpa [Category.assoc] using hcond_k)
  have hbase : (d ≫ Fa) ≫ p = (e ≫ Fb) ≫ p := by
    rw [Category.assoc, Category.assoc, ← ha, ← hb, reassoc_of% hde]
  have hrestr : t ≫ d ≫ Fa = t ≫ e ≫ Fb := by
    have h₁ := mi ≫= haj
    have h₂ := mk ≫= hbj
    simp only [mi, mk, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc] at h₁ h₂
    rw [h₁, h₂]
  exact hom_ext_of_surjective t (Surjective.surj (f := pullback.fst r j)) p
    (d ≫ Fa) (e ≫ Fb) hbase hrestr

/-- An `S`-morphism into a scheme étale over `S`, defined on a closed subscheme `Z ⊆ Y` with
the same underlying space as `Y`, extends to `Y`. -/
theorem exists_lift_of_surjective_closedImmersion
    {S X Y Z : Scheme.{u}} (p : X ⟶ S) [Etale p] (q : Y ⟶ S)
    (j : Z ⟶ Y) [IsClosedImmersion j] (hj : Function.Surjective j.base)
    (g : Z ⟶ X) (hg : j ≫ q = g ≫ p) :
    ∃ f : Y ⟶ X, f ≫ p = q ∧ j ≫ f = g := by
  classical
  choose U hyU F hFS hFj using fun y : Y => exists_lift_nbhd p q j hj g hg y
  let 𝒰 : Y.OpenCover.{u + 1} :=
    { I₀ := ULift.{u + 1} (↑Y)
      X i := U i.down
      f i := (U i.down).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun y ↦ ⟨ULift.up y, ⟨⟨y, hyU y⟩, rfl⟩⟩, fun _ ↦ inferInstance⟩ }
  have hcompat : ∀ i k,
      pullback.fst (𝒰.f i) (𝒰.f k) ≫ F i.down =
        pullback.snd (𝒰.f i) (𝒰.f k) ≫ F k.down := fun i k =>
    lift_eq_on_pullback p q j hj g (𝒰.f i) (𝒰.f k) (F i.down) (F k.down)
      (hFS i.down) (hFS k.down) (hFj i.down) (hFj k.down)
  let f : Y ⟶ X := 𝒰.glueMorphisms (fun i ↦ F i.down) hcompat
  refine ⟨f, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun i => ?_
    change (𝒰.f i ≫ 𝒰.glueMorphisms (fun i ↦ F i.down) hcompat) ≫ p = 𝒰.f i ≫ q
    rw [𝒰.ι_glueMorphisms]
    exact (hFS i.down).symm
  · let 𝒱 := 𝒰.pullback₂ j
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun i => ?_
    let i' : 𝒰.I₀ := i
    change pullback.snd (𝒰.f i') j ≫ j ≫ f = pullback.snd (𝒰.f i') j ≫ g
    calc
      pullback.snd (𝒰.f i') j ≫ j ≫ f = pullback.fst (𝒰.f i') j ≫ 𝒰.f i' ≫ f :=
        (pullback.condition_assoc f).symm
      _ = pullback.fst (𝒰.f i') j ≫ F i'.down := by
        dsimp [f]
        rw [𝒰.ι_glueMorphisms]
      _ = pullback.snd (𝒰.f i') j ≫ g := hFj i'.down

/-- Base change along a closed immersion with the same underlying space induces a bijection on
morphisms into an étale scheme. -/
@[stacks 025H,
  ega "IV 18.1.3",
  ega "IV 18.1.2" "fully faithful",
  sga "1 I 5.5",
  sga "1 IX 1.7" "fully faithful"]
theorem bijective_pullbackHom_of_etale
    {S S₀ : Scheme.{u}} (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : Function.Surjective i.base) (X Y : Over S) [Etale X.hom] :
    Function.Bijective (fun f : Y ⟶ X => (Over.pullback i).map f) := by
  have : Surjective i := ⟨hi⟩
  have hj : Function.Surjective (pullback.fst Y.hom i).base :=
    Surjective.surj (f := pullback.fst Y.hom i)
  refine ⟨fun f g h => ?_, fun g => ?_⟩
  · apply Over.OverMorphism.ext
    have hrestrict : pullback.fst Y.hom i ≫ f.left = pullback.fst Y.hom i ≫ g.left :=
      calc
        pullback.fst Y.hom i ≫ f.left =
            ((Over.pullback i).map f).left ≫ pullback.fst X.hom i := by
          simp [Over.pullback_map_left, pullback.lift_fst]
        _ = ((Over.pullback i).map g).left ≫ pullback.fst X.hom i := by
          rw [congrArg Over.Hom.left h]
        _ = pullback.fst Y.hom i ≫ g.left := by
          simp [Over.pullback_map_left, pullback.lift_fst]
    exact hom_ext_of_surjective (pullback.fst Y.hom i) hj X.hom f.left g.left
      ((Over.w f).trans (Over.w g).symm) hrestrict
  · have gw : g.left ≫ pullback.snd X.hom i = pullback.snd Y.hom i := by
      simpa only [Over.pullback_obj_hom] using g.w
    have hg : pullback.fst Y.hom i ≫ Y.hom = (g.left ≫ pullback.fst X.hom i) ≫ X.hom :=
      calc
        pullback.fst Y.hom i ≫ Y.hom = pullback.snd Y.hom i ≫ i := pullback.condition
        _ = g.left ≫ pullback.snd X.hom i ≫ i := ((reassoc_of% gw) i).symm
        _ = (g.left ≫ pullback.fst X.hom i) ≫ X.hom := by
          rw [Category.assoc, pullback.condition]
    obtain ⟨f, hfp, hfj⟩ := exists_lift_of_surjective_closedImmersion X.hom Y.hom
      (pullback.fst Y.hom i) hj (g.left ≫ pullback.fst X.hom i) hg
    refine ⟨Over.homMk f hfp, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [Over.pullback_map_left, pullback.lift_fst] using hfj
    · simpa [Over.pullback_map_left, pullback.lift_snd] using gw.symm

end Stacks.Etale

end
