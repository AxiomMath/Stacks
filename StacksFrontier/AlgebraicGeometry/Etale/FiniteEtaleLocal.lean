module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute

/-!
# A finite étale morphism is étale-locally a trivial covering

A finite étale morphism of schemes `f : X ⟶ S` is, étale-locally on `S`, a finite disjoint
union of copies of the base: for every `s : S` there is an étale neighbourhood `(U, u) ⟶ (S, s)`
and a decomposition `X ×_S U ≅ ∐_{i : ι} U` into finitely many copies of `U`, each mapping
isomorphically onto `U`. This is the scheme-theoretic form of the statement that a finite étale
morphism is a "topological covering space" in the étale topology.

The proof is a translation of the commutative-algebra statement
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`: a finite étale algebra of *constant* rank
becomes isomorphic to a finite product of copies of the base after a faithfully flat finite étale
base change. The reduction to constant rank is `Scheme.Hom.isLocallyConstant_finrank`, which lets
one shrink `S` to an affine open on which the rank of `f` is constant; the affine open is then
replaced by `Spec` of its ring of functions, and the morphism by `Spec` of a ring map, so that
the algebraic statement applies.

## Main definitions

* `Stacks.Etale.IsSplitCover` — a morphism `f : X ⟶ S` is a *split covering* if `X` is
  `S`-isomorphic to a finite disjoint union of copies of `S`, compatibly with `f`.

## Main results

* `Stacks.Etale.exists_etale_pullback_iso_sigma` — a finite étale morphism becomes a finite
  disjoint union of copies of the base after an étale base change through a neighbourhood of any
  given point.
* `Stacks.Etale.exists_etaleCover_pullback_iso_sigma` — the same statement packaged as a single
  étale covering of the base trivializing `f` on each member.
* `Stacks.Etale.exists_etale_isSplitCover_of_rankAtStalk` — the affine, constant-rank case.

## References

* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CommRingCat TensorProduct

universe u

namespace Stacks.Etale

/-- A morphism of schemes `f : X ⟶ S` is a *split covering* if `X` is, over `S`, a finite
disjoint union of copies of `S`: there is a finite type `ι` and an isomorphism
`e : X ≅ ∐ (fun _ : ι ↦ S)` which identifies `f` with the fold map of the coproduct. -/
@[ega "IV 18.2.7", sga "3 XXIV 8.4"]
def IsSplitCover {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (e : X ≅ ∐ fun _ : ι ↦ S),
    e.hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 S) = f

/-- Being a split covering depends only on the morphism up to isomorphism of its source. -/
lemma isSplitCover_iff_of_iso {X X' S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S} (e : X ≅ X')
    (he : e.hom ≫ f' = f) : IsSplitCover f ↔ IsSplitCover f' := by
  constructor
  · rintro ⟨ι, hι, e', he'⟩
    exact ⟨ι, hι, e.symm ≪≫ e', by
      rw [Iso.trans_hom, Category.assoc, he', ← he, Iso.symm_hom, Iso.inv_hom_id_assoc]⟩
  · rintro ⟨ι, hι, e', he'⟩
    exact ⟨ι, hι, e ≪≫ e', by rw [Iso.trans_hom, Category.assoc, he', he]⟩

/-- Whether the second projection of a pullback square is a split covering is a property of the
square, not of the particular model of the pullback. -/
lemma isSplitCover_snd_of_isPullback {P X Y S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) :
    IsSplitCover snd ↔ IsSplitCover (pullback.snd f g) :=
  isSplitCover_iff_of_iso h.isoPullback h.isoPullback_hom_snd

/-- Base changing along a composite `g ≫ h` may be carried out in two steps. -/
lemma isSplitCover_pullback_snd_comp {X S U W : Scheme.{u}} (f : X ⟶ S) (h : W ⟶ S)
    (g : U ⟶ W) :
    IsSplitCover (pullback.snd (pullback.snd f h) g) ↔ IsSplitCover (pullback.snd f (g ≫ h)) :=
  isSplitCover_iff_of_iso (pullbackLeftPullbackSndIso f h g)
    (pullbackLeftPullbackSndIso_hom_snd f h g)

/-- Precomposing with an isomorphism does not change the base change. -/
lemma isSplitCover_pullback_snd_iso_comp {X X' Y S : Scheme.{u}} (i : X' ≅ X) (f : X ⟶ S)
    (g : Y ⟶ S) :
    IsSplitCover (pullback.snd (i.hom ≫ f) g) ↔ IsSplitCover (pullback.snd f g) := by
  have H := (IsPullback.of_hasPullback f g).paste_horiz
    (IsPullback.of_horiz_isIso (fst := i.inv) (snd := f) (f := i.hom ≫ f) (g := 𝟙 S)
      ⟨by simp⟩)
  rw [Category.comp_id] at H
  exact (isSplitCover_snd_of_isPullback H).symm

/-! ### Trivial coverings coming from totally split algebras -/

/-- The canonical isomorphism `∐_{i : ι} Spec T ≅ Spec (ι → T)` for finite `ι` identifies the
structure morphism of `Spec (ι → T)` over `Spec T` with the fold map of the coproduct. -/
lemma sigmaSpec_comp_specMap_algebraMap (ι : Type u) [Finite ι] (T : Type u) [CommRing T] :
    sigmaSpec (fun _ : ι ↦ CommRingCat.of T) ≫
        Spec.map (CommRingCat.ofHom (algebraMap T (ι → T))) =
      Limits.Sigma.desc (fun _ ↦ 𝟙 (Spec (CommRingCat.of T))) := by
  refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
  rw [← Category.assoc, ι_sigmaSpec, ← Spec.map_comp, Limits.Sigma.ι_comp_desc]
  convert Spec.map_id (CommRingCat.of T) using 2
  ext t
  simp

/-- `Spec` of a finite product of copies of `T` is a split covering of `Spec T`. -/
lemma isSplitCover_specMap_algebraMap_pi (ι : Type u) [Finite ι] (T : Type u) [CommRing T] :
    IsSplitCover (Spec.map (CommRingCat.ofHom (algebraMap T (ι → T)))) := by
  refine ⟨ι, inferInstance, (asIso (sigmaSpec (fun _ : ι ↦ CommRingCat.of T))).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, ← sigmaSpec_comp_specMap_algebraMap ι T, IsIso.inv_hom_id_assoc]

/-- A finite totally split algebra gives a split covering on `Spec`. -/
lemma isSplitCover_specMap_algebraMap (T B : Type u) [CommRing T] [CommRing B] [Algebra T B]
    [Algebra.IsFiniteSplit T B] :
    IsSplitCover (Spec.map (CommRingCat.ofHom (algebraMap T B))) := by
  obtain ⟨m, ⟨φ₀⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T B
  let φ : B ≃ₐ[T] (ULift.{u} (Fin m) → T) :=
    φ₀.trans (AlgEquiv.piCongrLeft' T (fun _ : Fin m ↦ T) Equiv.ulift.symm)
  let κ : CommRingCat.of B ≅ CommRingCat.of (ULift.{u} (Fin m) → T) :=
    φ.toRingEquiv.toCommRingCatIso
  refine (isSplitCover_iff_of_iso
    (f' := Spec.map (CommRingCat.ofHom (algebraMap T (ULift.{u} (Fin m) → T))))
    { hom := Spec.map κ.inv
      inv := Spec.map κ.hom
      hom_inv_id := by rw [← Spec.map_comp, κ.hom_inv_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, κ.inv_hom_id, Spec.map_id] } ?_).mpr
    (isSplitCover_specMap_algebraMap_pi _ _)
  change Spec.map κ.inv ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  ext t
  simp [κ]

/-! ### The affine case -/

/-- If `A` is a finite étale `R`-algebra whose rank at every prime of `R` equals `n`, then there
is a faithfully flat étale `R`-algebra `T` such that `Spec A ×_{Spec R} Spec T` is a finite
disjoint union of copies of `Spec T`. -/
lemma exists_etale_isSplitCover_of_rankAtStalk (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Algebra.Etale R A] (n : ℕ)
    (hn : ∀ x, Module.rankAtStalk (R := R) A x = n) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra.Etale R T)
      (_ : Module.FaithfullyFlat R T),
      IsSplitCover (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T)))) := by
  obtain ⟨T, _, _, _, _, _, hT⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
    (R := R) (S := A) (n := n) (by funext x; simpa using hn x)
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine (isSplitCover_iff_of_iso
      (f' := Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A))))
      (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R T A) ?_).mpr
    (isSplitCover_specMap_algebraMap T (T ⊗[R] A))
  rw [Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]

/-- The constant-rank case for a morphism of affine schemes presented as `Spec` of a ring map. -/
@[sga "3 X 7.0.1" "special case"]
lemma exists_etale_surjective_isSplitCover_of_specMap {R A : CommRingCat.{u}} (φ : R ⟶ A)
    [IsFinite (Spec.map φ)] [Etale (Spec.map φ)] (n : ℕ)
    (hn : ∀ x, (Spec.map φ).finrank x = n) :
    ∃ (T : CommRingCat.{u}) (ψ : R ⟶ T) (_ : Etale (Spec.map ψ)) (_ : Surjective (Spec.map ψ)),
      IsSplitCover (pullback.snd (Spec.map φ) (Spec.map ψ)) := by
  have hfin : RingHom.Finite φ.hom := (IsFinite.SpecMap_iff φ).mp ‹_›
  have het : RingHom.Etale φ.hom := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  have hφ : CommRingCat.ofHom (algebraMap (R : Type u) (A : Type u)) = φ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact CommRingCat.ofHom_hom φ
  have hrk : ∀ x, Module.rankAtStalk (R := (R : Type u)) (A : Type u) x = n := by
    intro x
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap, hφ]
    exact hn _
  obtain ⟨T, _, _, _, _, hsplit⟩ :=
    exists_etale_isSplitCover_of_rankAtStalk (R : Type u) (A : Type u) n hrk
  refine ⟨CommRingCat.of T, CommRingCat.ofHom (algebraMap (R : Type u) T), ?_,
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr
      (by rw [CommRingCat.hom_ofHom]; exact RingHom.etale_algebraMap.mpr ‹_›)
  · rwa [← hφ]

/-- The constant-rank case over an affine base: a finite étale morphism of constant rank over an
affine scheme becomes a split covering after a surjective étale base change. -/
@[sga "3 X 7.0.1" "special case"]
lemma exists_etale_surjective_isSplitCover_of_isAffine {P V : Scheme.{u}} [IsAffine V]
    (f : P ⟶ V) [IsFinite f] [Etale f] (n : ℕ) (hn : ∀ y, f.finrank y = n) :
    ∃ (U : Scheme.{u}) (g : U ⟶ V) (_ : Etale g) (_ : Surjective g),
      IsSplitCover (pullback.snd f g) := by
  have hrk₁ : ∀ y, (pullback.snd f V.isoSpec.inv).finrank y = n := fun y ↦ by
    rw [Scheme.Hom.finrank_pullback_snd]; exact hn _
  have hPaff : IsAffine (pullback f V.isoSpec.inv) :=
    isAffine_of_isAffineHom (pullback.snd f V.isoSpec.inv)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    ((pullback f V.isoSpec.inv).isoSpec.inv ≫ pullback.snd f V.isoSpec.inv)
  have hcomp : (pullback f V.isoSpec.inv).isoSpec.hom ≫ Spec.map φ
      = pullback.snd f V.isoSpec.inv := by rw [hφ, Iso.hom_inv_id_assoc]
  have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have h2 : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hrk : ∀ x, (Spec.map φ).finrank x = n := fun x ↦ by
    rw [hφ, Scheme.Hom.finrank_comp_left_of_isIso]; exact hrk₁ x
  obtain ⟨T, ψ, _, _, hsplit⟩ := exists_etale_surjective_isSplitCover_of_specMap φ n hrk
  refine ⟨Spec T, Spec.map ψ ≫ V.isoSpec.inv, inferInstance, inferInstance, ?_⟩
  have h3 : IsSplitCover (pullback.snd
      ((pullback f V.isoSpec.inv).isoSpec.hom ≫ Spec.map φ) (Spec.map ψ)) :=
    (isSplitCover_pullback_snd_iso_comp _ (Spec.map φ) (Spec.map ψ)).mpr hsplit
  rw [hcomp] at h3
  exact (isSplitCover_pullback_snd_comp f V.isoSpec.inv (Spec.map ψ)).mp h3

/-! ### The general case -/

/-- A finite étale morphism becomes a split covering after an étale base change through a
neighbourhood of any prescribed point of the base. -/
lemma exists_etale_isSplitCover {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (_ : Etale g) (u : U) (_ : g u = s),
      IsSplitCover (pullback.snd f g) := by
  have hopen : IsOpen {y : S | f.finrank y = f.finrank s} :=
    (Scheme.Hom.isLocallyConstant_finrank f).isOpen_fiber _
  obtain ⟨V, hV, hsV, hVle⟩ : ∃ V : S.Opens, IsAffineOpen V ∧ s ∈ V ∧
      ∀ y ∈ V, f.finrank y = f.finrank s := by
    obtain ⟨V, hV, hsV, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (U := ⟨_, hopen⟩) (x := s) rfl
    exact ⟨V, hV, hsV, fun y hy ↦ hVle hy⟩
  have : IsAffine V.toScheme := hV
  have hrank : ∀ y, (pullback.snd f V.ι).finrank y = f.finrank s := fun y ↦ by
    rw [Scheme.Hom.finrank_pullback_snd]; exact hVle _ y.2
  obtain ⟨U, g, _, _, hsplit⟩ :=
    exists_etale_surjective_isSplitCover_of_isAffine (pullback.snd f V.ι) _ hrank
  obtain ⟨u, hu⟩ := g.surjective ⟨s, hsV⟩
  refine ⟨U, g ≫ V.ι, inferInstance, u, ?_,
    (isSplitCover_pullback_snd_comp f V.ι g).mp hsplit⟩
  rw [Scheme.Hom.comp_apply, hu]
  rfl

/-- Let `f : X ⟶ S` be a finite étale morphism of schemes and let `s : S`. There is an étale
neighbourhood `g : U ⟶ S` of `s`, a finite index type `ι` and an isomorphism
`X ×_S U ≅ ∐_{i : ι} U` over `U`; that is, `X` becomes a finite disjoint union of copies of the
base, each mapping isomorphically onto it, after an étale base change near `s`. -/
@[stacks 04HN]
theorem exists_etale_pullback_iso_sigma {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (_ : Etale g) (u : U) (_ : g u = s) (ι : Type u)
      (_ : Finite ι) (e : pullback f g ≅ ∐ fun _ : ι ↦ U),
      e.hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 U) = pullback.snd f g :=
  exists_etale_isSplitCover f s

/-- A finite étale morphism `f : X ⟶ S` admits an étale covering `𝒰` of `S` together with, for
each member `i`, a finite index type `ι i` and an isomorphism `X ×_S 𝒰.X i ≅ ∐_{ι i} 𝒰.X i` over
`𝒰.X i`. -/
@[stacks 04HN "étale covering form"]
theorem exists_etaleCover_pullback_iso_sigma {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Etale f] :
    ∃ (𝒰 : S.Cover.{u} (Scheme.precoverage @Etale)) (ι : 𝒰.I₀ → Type u)
      (_ : ∀ i, Finite (ι i)) (e : ∀ i, pullback f (𝒰.f i) ≅ ∐ fun _ : ι i ↦ 𝒰.X i),
      ∀ i, (e i).hom ≫ Limits.Sigma.desc (fun _ ↦ 𝟙 (𝒰.X i)) = pullback.snd f (𝒰.f i) := by
  choose U g hg u hu ι hι e he using fun s : S ↦ exists_etale_isSplitCover f s
  exact ⟨Scheme.Cover.mkOfCovers (S : Type u) U g (fun s ↦ ⟨s, u s, hu s⟩) hg, ι, hι, e, he⟩

end Stacks.Etale
