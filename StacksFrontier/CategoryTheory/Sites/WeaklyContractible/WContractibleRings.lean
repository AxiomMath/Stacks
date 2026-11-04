module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly contractible objects and w-contractible rings

Stacks tag 090L calls an object `T` of a site *weakly contractible* when every surjection
of sheaves of sets is surjective on sections over `T`; this is `IsWeaklyContractibleObj`
for the big pro-etale site of schemes.  The main result proved here is Stacks tag 098H
(Lemma 61.13.2): for `T = Spec A`, weak contractibility of `T` is equivalent both to `A`
being w-contractible (every faithfully flat weakly etale `A → B` has a retraction) and to
every pro-etale covering of `T` being refined by a finite Zariski decomposition
`T = ∐_{i} U_i` of `T` into pairwise disjoint clopen pieces.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

namespace ProetaleWContractible

universe u v

/-- **Definition 1 (Weakly etale ring map).**
A ring map `A → B` is *weakly etale* (Stacks Tag `094N`) if both the structure map `A → B`
and the multiplication map `B ⊗_A B → B` are flat.  Concretely, `B` is a flat `A`-module
and the multiplication homomorphism `μ : B ⊗_A B → B`, `a ⊗ b ↦ a b`
(`Algebra.TensorProduct.lmul'`), is flat.  This matches the form used in Mathlib's
`Algebra.weaklyEtale_iff`. -/
def IsWeaklyEtale (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Module.Flat A B ∧ (Algebra.TensorProduct.lmul' A (S := B)).Flat

/-- **Definition 3 (Retraction).**
A ring map `A → B` (here the structure map `algebraMap A B`) *has a retraction* if there
exists a ring map `σ : B → A` such that the composite `A → B → A` is the identity on `A`.
For an `A`-algebra, this is equivalent to the existence of an `A`-algebra homomorphism
`σ : B →ₐ[A] A`: such a `σ` automatically satisfies `σ (algebraMap A B a) = a`. -/
def HasRetraction (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  Nonempty (B →ₐ[A] A)

/-- Correctness of `HasRetraction`: it is equivalent to the existence of a ring
homomorphism `σ : B → A` that is a one-sided inverse to the structure map `A → B`. -/
theorem hasRetraction_iff (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    HasRetraction A B ↔
      ∃ σ : B →+* A, σ.comp (algebraMap A B) = RingHom.id A := by
  constructor
  · rintro ⟨σ⟩
    refine ⟨σ.toRingHom, ?_⟩
    ext a
    simp
  · rintro ⟨σ, hσ⟩
    refine ⟨⟨σ, ?_⟩⟩
    intro a
    have := RingHom.congr_fun hσ a
    simpa using this

/-- **Definition 4 (w-contractible ring; Stacks Tag `0981`).**
A ring `A` is *w-contractible* if every faithfully flat weakly etale ring map `A → B` has a
retraction.  We quantify over all `A`-algebra structures on all rings `B`; the universe of
`B` is the implicit universe parameter `w` of this definition, so the condition is not
restricted to a fixed universe. -/
@[stacks 0981]
def IsWContractible.{w} (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type w) [CommRing B] [Algebra A B],
    IsWeaklyEtale A B → Module.FaithfullyFlat A B → HasRetraction A B

/-!
### Site-theoretic definitions

`Sch_{pro-etale}` is modelled by the universe-polymorphic category `Scheme.{u}` equipped
with the big pro-etale Grothendieck topology `Scheme.proetaleTopology` (Stacks Tag `098G`).
The topology is subcanonical (Stacks Tag `098Z`).  Sheaves of sets are valued in `Type u`,
the universe of the morphism sets.
-/

/-- **Definition 8 / 9 (Weakly contractible object of the big pro-etale site;
Stacks Tags `00WM`, `090L`).**
An object `T` of the big pro-etale site is *weakly contractible* if for every surjection of
sheaves of sets `φ : F → G` on the site, the induced map on sections `F(T) → G(T)` is
surjective.  A morphism of sheaves of sets is a *surjection* iff it is locally surjective
(an epimorphism of sheaves), which is `CategoryTheory.Sheaf.IsLocallySurjective`. -/
def IsWeaklyContractibleObj (T : Scheme.{u}) : Prop :=
  ∀ (F G : Sheaf Scheme.proetaleTopology.{u} (Type u)) (φ : F ⟶ G),
    Sheaf.IsLocallySurjective φ → Function.Surjective (φ.hom.app (op T))

/-!
### Zariski clopen-decomposition coverings

A *Zariski covering of `T` of the form `T = ∐_{i=1,…,n} U_i`* is a finite family of open
immersions `U_i ↪ T` whose images are pairwise disjoint open-and-closed subsets covering
`T`.  We capture such a covering by the property `IsClopenDecompositionCover` of a finite
family of morphisms.  Condition (3) says that every pro-etale covering sieve of `T` is
*refined* by (i.e. contains) such a Zariski covering. -/

/-- A finite family of morphisms `f i : U i ⟶ T` is a *clopen decomposition* of `T` if each
`f i` is an open immersion and the images are pairwise disjoint clopen subsets covering `T`,
so that `T = ∐_{i=1,…,n} U_i`. -/
structure IsClopenDecompositionCover {n : ℕ} {T : Scheme.{u}}
    (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ T) : Prop where
  /-- Each `f i` is an open immersion. -/
  openImmersion : ∀ i, IsOpenImmersion (f i)
  /-- The image of each `f i` is clopen in `T`. -/
  clopen : ∀ i, IsClopen (Set.range (f i).base)
  /-- The images are pairwise disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (f i).base) (Set.range (f j).base)
  /-- The images cover `T`. -/
  cover : (⋃ i, Set.range (f i).base) = Set.univ

/-- A Zariski clopen decomposition `{f i : U i → T}` *refines* a sieve `S` on `T` if every
arrow `f i` belongs to `S` (equivalently the sieve it generates is contained in `S`).
Because `S` is a sieve (closed under precomposition), requiring each `f i ∈ S` is equivalent
to the "refinement" notion of Definition 6, which asks only that each `U i → T` factors
through some member of the covering generating `S`. -/
def ClopenDecompositionRefines {n : ℕ} {T : Scheme.{u}}
    (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ T) (S : Sieve T) : Prop :=
  ∀ i, S.arrows (f i)

/-- **Condition 3.**
Every pro-etale covering of `T` can be refined by a Zariski covering of the form
`T = ∐_{i=1,…,n} U_i`: for every pro-etale covering sieve `S` of `T` there exist `n`, a
family of schemes `U : Fin n → Scheme`, and open immersions `f i : U i → T` forming a clopen
decomposition of `T` that refines `S`. -/
def EveryProetaleCoverHasZariskiRefinement (T : Scheme.{u}) : Prop :=
  ∀ S ∈ Scheme.proetaleTopology.sieves T,
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ T),
      IsClopenDecompositionCover U f ∧ ClopenDecompositionRefines U f S

/-! ### Affine schemes and their structure morphisms

`T = Spec A` is `Scheme.Spec.obj (op (CommRingCat.of A))`. -/

/-- The affine scheme `Spec A` associated to a ring `A`. -/
@[ega "I 1.7.1", ega "I 10.10.1", sga "5 III 1.1"]
noncomputable def specOf (A : Type u) [CommRing A] : Scheme.{u} :=
  Scheme.Spec.obj (op (CommRingCat.of A))

/-- The structure morphism `Spec B → Spec A` induced by an `A`-algebra structure on `B`,
i.e. `Scheme.Spec.map (algebraMap A B)ᵒᵖ`. -/
@[ega "I 1.7.2", ega "I 3.3.13", ega "IV 1.9.2"]
noncomputable def specMapOf (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    specOf B ⟶ specOf A :=
  Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op

/-!
### Decomposition lemmas for `(2) ⇒ (1)` (the `h21` implication of `main_theorem`)

The implication `IsWeaklyContractibleObj (specOf A) → IsWContractible A` is proved by the
following *direct* argument (a simplification, in the affine ring case, of the Stacks Tag
`0983`/`098F` proof, which avoids constructing the auxiliary w-contractible cover `D`):

Given an arbitrary faithfully flat weakly etale `A`-algebra `B`, the single morphism
`Spec B → Spec A` is a pro-etale covering (`proetaleCoveringSieve_of_ffWeaklyEtale`), so the
representable morphism of sheaves `h_{Spec B} → h_{Spec A}` is locally surjective; weak
contractibility of `Spec A` then lifts `𝟙 (Spec A)` to a section `s : Spec A → Spec B`
(`exists_section_of_weaklyContractibleObj`); and a section corresponds, via the fully
faithful `Spec` functor, to an `A`-algebra retraction `B →ₐ[A] A`
(`hasRetraction_of_section`).
-/

/-- A weakly etale ring map `A → B` induces a weakly etale morphism `Spec B → Spec A`. -/
private lemma weaklyEtale_specMapOf_of_isWeaklyEtale {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hwe : IsWeaklyEtale A B) : AlgebraicGeometry.WeaklyEtale (specMapOf A B) := by
  have hFlat : AlgebraicGeometry.Flat (specMapOf A B) := by
    change AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    exact RingHom.flat_algebraMap_iff.mpr hwe.1
  have hDiagFlat : AlgebraicGeometry.Flat (pullback.diagonal (specMapOf A B)) := by
    change AlgebraicGeometry.Flat
      (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    rw [diagonal_SpecMap A B]
    have h1 : AlgebraicGeometry.Flat
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
      exact hwe.2
    exact MorphismProperty.comp_mem _ _ _ h1 inferInstance
  exact (weaklyEtale_iff _).mpr ⟨hFlat, hDiagFlat⟩

/-- If `Spec B → Spec A` is weakly etale then the ring map `A → B` is weakly etale. -/
private lemma isWeaklyEtale_of_weaklyEtale_specMapOf {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hwe : AlgebraicGeometry.WeaklyEtale (specMapOf A B)) : IsWeaklyEtale A B := by
  obtain ⟨hflat, hdiag⟩ := (weaklyEtale_iff (specMapOf A B)).mp hwe
  have hflat' : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := hflat
  have hdiag' : AlgebraicGeometry.Flat
      (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := hdiag
  refine ⟨RingHom.flat_algebraMap_iff.mp
    ((HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mp hflat'), ?_⟩
  rw [diagonal_SpecMap A B] at hdiag'
  have hcomp : AlgebraicGeometry.Flat
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)) :=
    (MorphismProperty.cancel_right_of_respectsIso (P := @AlgebraicGeometry.Flat) _ _).mp hdiag'
  exact (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mp hcomp

/-- **(2) ⇒ (1), step 1.**  A faithfully flat weakly etale ring map `A → B` gives a pro-etale
covering sieve of `T = Spec A`: the sieve generated by the single arrow `Spec B → Spec A`.
A weakly etale (Stacks `094N`) faithfully flat (hence surjective on `Spec`) ring map is a
pro-etale cover (Stacks `0989`/`098B`); use Mathlib's `Scheme.proetalePrecoverage` /
`Scheme.proetaleTopology` infrastructure (`AlgebraicGeometry.Sites.Proetale`), the
translation `IsWeaklyEtale A B → AlgebraicGeometry.WeaklyEtale (specMapOf A B)`
(`Algebra.weaklyEtale_iff`/`HasRingHomProperty`), and faithful flatness ⇒ surjectivity of
`Spec`. -/
lemma proetaleCoveringSieve_of_ffWeaklyEtale (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (hwe : IsWeaklyEtale A B) (hff : Module.FaithfullyFlat A B) :
    Sieve.ofArrows (fun _ : Unit => specOf B) (fun _ => specMapOf A B)
      ∈ Scheme.proetaleTopology.sieves (specOf A) := by
  set f : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B) with hf
  -- faithfully flat ring hom
  have hffhom : f.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  have hfs := (flat_and_surjective_SpecMap_iff f).mpr hffhom
  have hSurj : AlgebraicGeometry.Surjective (Spec.map f) := hfs.2
  have hQC : QuasiCompact (Spec.map f) := quasiCompact_of_compactSpace _
  have hWE : AlgebraicGeometry.WeaklyEtale (Spec.map f) :=
    weaklyEtale_specMapOf_of_isWeaklyEtale hwe
  -- the singleton presieve is a proetale covering
  have hcov' : Presieve.singleton (Spec.map f) ∈
      Scheme.proetalePrecoverage.coverings (specOf A) :=
    Scheme.Hom.singleton_mem_propQCPrecoverage hWE
  -- the `ofArrows` presieve equals the singleton presieve
  have hpre : Presieve.ofArrows (fun _ : Unit => specOf B) (fun _ => specMapOf A B)
      = Presieve.singleton (Spec.map f) := by
    funext Z g
    apply propext
    constructor
    · rintro ⟨_⟩; exact Presieve.singleton.mk
    · rintro ⟨⟩; exact Presieve.ofArrows.mk ()
  -- assemble: membership in the saturated sieves of the precoverage
  show Scheme.proetalePrecoverage.Saturate (specOf A)
    (Sieve.ofArrows (fun _ : Unit => specOf B) (fun _ => specMapOf A B))
  have hsieve : Sieve.ofArrows (fun _ : Unit => specOf B) (fun _ => specMapOf A B)
      = Sieve.generate (Presieve.singleton (Spec.map f)) := by
    rw [← hpre]
  rw [hsieve]
  exact Precoverage.Saturate.of (specOf A) _ hcov'

/-- **(2) ⇒ (1), step 2.**  If `Spec A` is a weakly contractible object and the single arrow
`Spec B → Spec A` generates a pro-etale covering sieve, then there is a section
`s : Spec A → Spec B` of `specMapOf A B`.
Apply weak contractibility (`h2`) to the sheaf morphism `h_{Spec B} → h_{Spec A}` (the
sheafified representable map; the pro-etale topology is subcanonical, Stacks `098Z`, so the
representables are sheaves).  The covering hypothesis `hcov` makes this morphism locally
surjective (`GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_…`); surjectivity on
`T`-sections then lifts `𝟙 (specOf A) ∈ h_{Spec A}(specOf A)` to an element of
`h_{Spec B}(specOf A) = (specOf A ⟶ specOf B)`, which is the desired section. -/
lemma exists_section_of_weaklyContractibleObj (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (h2 : IsWeaklyContractibleObj (specOf A))
    (hcov : Sieve.ofArrows (fun _ : Unit => specOf B) (fun _ => specMapOf A B)
      ∈ Scheme.proetaleTopology.sieves (specOf A)) :
    ∃ s : specOf A ⟶ specOf B, s ≫ specMapOf A B = 𝟙 (specOf A) := by
  set g : specOf B ⟶ specOf A := specMapOf A B with hg
  set J := Scheme.proetaleTopology.{u}
  -- The representable sheaf morphism `h_{Spec B} → h_{Spec A}`.
  set φ : J.yoneda.obj (specOf B) ⟶ J.yoneda.obj (specOf A) := J.yoneda.map g with hφ
  -- `φ` is locally surjective because `g` generates a covering sieve.
  have hls : Sheaf.IsLocallySurjective φ := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    -- reduce to local surjectivity of the underlying presheaf map `yoneda.map g`
    have hpsh : (sheafToPresheaf J (Type u)).map φ = yoneda.map g := by
      simp only [hφ]; exact J.yoneda_map_hom g
    rw [hpsh]
    refine ⟨?_⟩
    intro V s
    -- `imageSieve (yoneda.map g) s = pullback of the covering sieve along `s`
    have hsub : (Sieve.ofArrows (fun _ : Unit => specOf B) (fun _ => g)).pullback s
        ≤ Presheaf.imageSieve (yoneda.map g) s := by
      intro W i hi
      -- `hi : (ofArrows ...).pullback s` at `i`, i.e. `i ≫ s ∈ ofArrows`
      rw [Sieve.pullback_apply, Sieve.ofArrows, Sieve.generate_apply] at hi
      obtain ⟨Y, h, _, ⟨_⟩, hcomp⟩ := hi
      -- hcomp : h ≫ g = i ≫ s
      refine ⟨h, ?_⟩
      -- goal: (yoneda.map g).app _ h = (yoneda.obj _).map i.op s
      simp only [yoneda_map_app, yoneda_obj_map]
      show h ≫ g = i ≫ s
      exact hcomp
    refine J.superset_covering hsub ?_
    exact J.pullback_stable s hcov
  -- Apply weak contractibility to lift `𝟙 (specOf A)`.
  have hsurj := h2 _ _ φ hls
  obtain ⟨s, hs⟩ := hsurj (𝟙 (specOf A))
  refine ⟨s, ?_⟩
  -- compute the action of `φ.hom.app` on `s`
  have happ : φ.hom.app (op (specOf A)) s = s ≫ g := by
    rw [hφ, J.yoneda_map_hom g, yoneda_map_app]
    rfl
  rwa [happ] at hs

/-- **(2) ⇒ (1), step 3.**  A section `s : Spec A → Spec B` of `specMapOf A B` yields an
`A`-algebra retraction `B →ₐ[A] A`, hence `HasRetraction A B`.
`Spec` is fully faithful (`AlgebraicGeometry.Spec.fullyFaithful`, `Spec.homEquiv`); the
section `s` corresponds to a ring map `σ : B → A` with `σ ∘ algebraMap A B = id`, i.e. an
`A`-algebra map, via `hasRetraction_iff`. -/
lemma hasRetraction_of_section (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (s : specOf A ⟶ specOf B) (hs : s ≫ specMapOf A B = 𝟙 (specOf A)) :
    HasRetraction A B := by
  rw [hasRetraction_iff]
  let ff := Spec.fullyFaithful
  let key : op (CommRingCat.of A) ⟶ op (CommRingCat.of B) := ff.preimage s
  refine ⟨key.unop.hom, ?_⟩
  -- Pull the equation `hs` back through the fully faithful functor `Spec`.
  have hmap : key ≫ (CommRingCat.ofHom (algebraMap A B)).op
      = 𝟙 (op (CommRingCat.of A)) := by
    apply ff.map_injective
    rw [Functor.map_comp, ff.map_preimage, CategoryTheory.Functor.map_id]
    exact hs
  -- Take `unop` to get the equation in `CommRingCat`.
  have hmap' := congrArg Quiver.Hom.unop hmap
  simp only [unop_comp, Quiver.Hom.unop_op, unop_id] at hmap'
  -- `hmap'` : CommRingCat.ofHom (algebraMap A B) ≫ key.unop = 𝟙 (CommRingCat.of A)
  simpa using congrArg CommRingCat.Hom.hom hmap'

/-- **(3) ⇒ (1).**  Stacks Tag `098F` (Lemma 61.13.1), converse direction.
If every pro-etale covering of `T = Spec A` is refined by a Zariski clopen decomposition,
then `A` is w-contractible. -/
lemma isWContractible_of_zariskiRefinement (A : Type u) [CommRing A]
    (h3 : EveryProetaleCoverHasZariskiRefinement (specOf A)) :
    IsWContractible.{u, u} A := by
  intro B _ _ hwe hff
  -- The single arrow `Spec B → Spec A` generates a pro-etale covering sieve.
  have hS := proetaleCoveringSieve_of_ffWeaklyEtale A B hwe hff
  -- Apply the Zariski clopen-decomposition refinement to this sieve.
  obtain ⟨n, U, f, hcov, href⟩ := h3 _ hS
  -- Each `f i ∈ S` factors through `specMapOf A B`, giving `g i : U i ⟶ specOf B`.
  have hfact : ∀ i, ∃ g : U i ⟶ specOf B, g ≫ specMapOf A B = f i := by
    intro i
    have hi := href i
    rw [Sieve.ofArrows, Sieve.generate_apply] at hi
    obtain ⟨Y, h, p, hp, hcomp⟩ := hi
    cases hp with
    | mk u => exact ⟨h, hcomp⟩
  choose g hg using hfact
  -- The clopen decomposition is an open cover of `specOf A`.
  set 𝒰 : (specOf A).OpenCover := Scheme.Cover.mkOfCovers (Fin n) U f
    (by intro x
        have hx : x ∈ (⋃ i, Set.range (f i).base) := by rw [hcov.cover]; trivial
        simp only [Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, hy⟩ := hx
        exact ⟨i, y, hy⟩)
    (fun j => hcov.openImmersion j) with h𝒰
  have hf𝒰 : ∀ i, 𝒰.f i = f i := fun i => rfl
  -- The `g i` agree on overlaps: each overlap is empty (disjoint) or `f i` is mono.
  have hcompat : ∀ x y : 𝒰.I₀,
      pullback.fst (𝒰.f x) (𝒰.f y) ≫ g x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ g y := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      have : Mono (𝒰.f x) := (hcov.openImmersion x).mono
      rw [fst_eq_snd_of_mono_eq (𝒰.f x)]
    · have hemp : IsEmpty (pullback (𝒰.f x) (𝒰.f y) : Scheme).carrier :=
        Scheme.isEmpty_pullback (𝒰.f x) (𝒰.f y) (hcov.disjoint x y hxy)
      obtain ⟨hinit⟩ := AlgebraicGeometry.isInitial_iff_isEmpty.mpr hemp
      exact hinit.hom_ext _ _
  -- Glue the `g i` into a single section `s : specOf A ⟶ specOf B`.
  refine hasRetraction_of_section A B (𝒰.glueMorphisms g hcompat) ?_
  -- Check `s ≫ specMapOf A B = 𝟙` piecewise on the cover.
  apply 𝒰.hom_ext
  intro x
  rw [← Category.assoc, 𝒰.ι_glueMorphisms g hcompat x, hg x, Category.comp_id, hf𝒰 x]

/-- The value of a sheaf at an empty scheme is a subsingleton: the empty sieve covers an
empty scheme, so the section set is terminal in `Type`. -/
lemma subsingleton_sheaf_obj_of_isEmpty
    (F : Sheaf Scheme.proetaleTopology.{u} (Type u))
    (W : Scheme.{u}) (hW : IsEmpty W.carrier) :
    Subsingleton (F.obj.obj (op W)) := by
  have : IsEmpty W := hW
  have hbot : (⊥ : Sieve W) ∈ Scheme.proetaleTopology.{u}.sieves W :=
    Scheme.bot_mem_propQCTopology (P := @WeaklyEtale) W
  have hterm := Sheaf.isTerminalOfBotCover F W hbot
  have := (Limits.Types.isTerminalEquivUnique _) hterm
  infer_instance

/-- **(3) ⇒ (2).**  If every pro-etale covering of `T = Spec A` is refined by a Zariski
clopen decomposition, then `T` is a weakly contractible object of the big pro-etale site.

Given a locally surjective sheaf morphism `φ : F → G` and a section `s ∈ G(T)`, the image
sieve `S = imageSieve φ s` is a covering sieve (`Presheaf.imageSieve_mem`).  By `h3` it is
refined by a Zariski clopen decomposition `T = ∐ U_i`, each `f i ∈ S`, giving lifts
`t i ∈ F(U_i)` with `φ(t i) = s|_{U_i}`.  The disjoint clopen family `{f i}` is itself a
pro-etale covering sieve (finite jointly surjective family of weakly etale, quasi-compact
open immersions), so `F` and `G` are sheaves for it.  Since the pieces are pairwise
disjoint, the overlaps are empty, so the family `(t i)` is compatible and amalgamates to a
global `t ∈ F(T)`; naturality of `φ` and separatedness of `G` give `φ(t) = s`. -/
lemma isWeaklyContractibleObj_of_zariskiRefinement (A : Type u) [CommRing A]
    (h3 : EveryProetaleCoverHasZariskiRefinement (specOf A)) :
    IsWeaklyContractibleObj (specOf A) := by
  intro F G φ hφ s
  -- The image sieve of φ at s is a covering sieve.
  have hS : Presheaf.imageSieve φ.hom s ∈ Scheme.proetaleTopology.{u}.sieves (specOf A) :=
    Presheaf.imageSieve_mem (J := Scheme.proetaleTopology.{u}) φ.hom (U := op (specOf A)) s
  -- Apply the Zariski refinement.
  obtain ⟨n, U, f, hcov, href⟩ := h3 _ hS
  -- Each f i ∈ S, giving a lift t i.
  have hlift : ∀ i, ∃ t : F.obj.obj (op (U i)),
      φ.hom.app (op (U i)) t = G.obj.map (f i).op s := fun i => href i
  choose t ht using hlift
  -- Each f i is an open immersion, hence weakly etale; and quasi-compact (U i clopen in
  -- the affine, hence compact).
  have hOI : ∀ i, IsOpenImmersion (f i) := hcov.openImmersion
  have : IsAffine (specOf A) := by unfold specOf; infer_instance
  have hCompact : ∀ i, CompactSpace (U i) := by
    intro i
    have hemb : Topology.IsOpenEmbedding (f i).base := (f i).isOpenEmbedding
    have hce : Topology.IsClosedEmbedding (f i).base := ⟨hemb.isEmbedding, (hcov.clopen i).1⟩
    exact hce.compactSpace
  have hQC : ∀ i, QuasiCompact (f i) := fun i => quasiCompact_of_compactSpace (f i)
  have hWE : ∀ i, WeaklyEtale (f i) := by intro i; have := hOI i; infer_instance
  -- The disjoint clopen family generates a pro-etale covering sieve.
  have hSₐ : Sieve.ofArrows U f ∈ Scheme.proetaleTopology.{u}.sieves (specOf A) := by
    have hsurj : ∀ (x : ↥(specOf A)), ∃ i y, (f i).base y = x := by
      intro x
      have hx : x ∈ (⋃ i, Set.range (f i).base) := by rw [hcov.cover]; trivial
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨i, y, hy⟩ := hx
      exact ⟨i, y, hy⟩
    set 𝒰 := Scheme.Cover.mkOfCovers (ULift.{u} (Fin n)) (fun i => U i.down) (fun i => f i.down)
      (by intro x; obtain ⟨i, y, hy⟩ := hsurj x; exact ⟨ULift.up i, y, hy⟩)
      (fun j => hWE j.down) with h𝒰
    have hI : ∀ i : 𝒰.I₀, QuasiCompact (𝒰.f i) := fun i => hQC i.down
    have : Finite 𝒰.I₀ := by change Finite (ULift.{u} (Fin n)); infer_instance
    have hQCC : QuasiCompactCover 𝒰.toPreZeroHypercover := QuasiCompactCover.of_finite
    have hmem := Scheme.Cover.mem_propQCTopology (P := @WeaklyEtale) 𝒰
    have hsieve : Sieve.ofArrows 𝒰.X 𝒰.f = Sieve.ofArrows U f := by
      apply le_antisymm
      · rw [Sieve.ofArrows, Sieve.ofArrows, Sieve.generate_le_iff]
        rintro Y g ⟨i⟩
        exact ⟨U i.down, 𝟙 _, f i.down, ⟨i.down⟩, by simp only [Category.id_comp]; rfl⟩
      · rw [Sieve.ofArrows, Sieve.ofArrows, Sieve.generate_le_iff]
        rintro Y g ⟨i⟩
        exact ⟨U i, 𝟙 _, f i, ⟨ULift.up i⟩, by simp⟩
    rw [hsieve] at hmem
    exact hmem
  -- The family `(t i)` is compatible: overlaps are empty (disjoint) or `f i` is mono.
  have htcompat : Presieve.Arrows.Compatible F.obj f t := by
    intro i j Z gi gj hcomp
    by_cases hij : i = j
    · subst hij
      have : Mono (f i) := (hOI i).mono
      have : gi = gj := by rwa [cancel_mono] at hcomp
      rw [this]
    · have hZempty : IsEmpty Z.carrier := by
        constructor
        intro z
        have h1 : (f i).base (gi.base z) = (f j).base (gj.base z) := by
          simpa using congrArg (fun m => m.base z) hcomp
        have hmem_i : (f i).base (gi.base z) ∈ Set.range (f i).base := ⟨_, rfl⟩
        have hmem_j : (f i).base (gi.base z) ∈ Set.range (f j).base := h1 ▸ ⟨_, rfl⟩
        exact (hcov.disjoint i j hij).le_bot ⟨hmem_i, hmem_j⟩
      have := subsingleton_sheaf_obj_of_isEmpty F Z hZempty
      exact Subsingleton.elim _ _
  -- `F` and `G` are sheaves for the disjoint clopen family.
  have hFsh : Presieve.IsSheafFor F.obj (Presieve.ofArrows U f) := by
    rw [Presieve.isSheafFor_iff_generate]; exact F.property.isSheafFor _ hSₐ
  have hGsh : Presieve.IsSheafFor G.obj (Presieve.ofArrows U f) := by
    rw [Presieve.isSheafFor_iff_generate]; exact G.property.isSheafFor _ hSₐ
  -- Amalgamate `(t i)` to a global section `tT`.
  rw [Presieve.isSheafFor_arrows_iff] at hFsh
  obtain ⟨tT, htT, _⟩ := hFsh t htcompat
  refine ⟨tT, ?_⟩
  -- Use separatedness of `G`: `φ(tT)` and `s` restrict to the same family.
  rw [Presieve.isSheafFor_arrows_iff] at hGsh
  have hgcompat : Presieve.Arrows.Compatible G.obj f (fun i => G.obj.map (f i).op s) := by
    intro i j Z gi gj hcomp
    simp only
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, hcomp]
  obtain ⟨tt, _, htt_uniq⟩ := hGsh (fun i => G.obj.map (f i).op s) hgcompat
  have hamalg1 : ∀ i, G.obj.map (f i).op (φ.hom.app (op (specOf A)) tT)
      = G.obj.map (f i).op s := by
    intro i
    have hnat := NatTrans.naturality_apply φ.hom (f i).op tT
    rw [← hnat, htT i, ht i]
  have hamalg2 : ∀ i, G.obj.map (f i).op s = G.obj.map (f i).op s := fun i => rfl
  rw [htt_uniq _ hamalg1, htt_uniq _ hamalg2]

/-!
### Decomposition lemmas for `(1) ⇒ (3)` (the `h13` implication of `main_theorem`)

The forward direction (Stacks Tag `098F`, using Tag `098D`) runs through three sub-lemmas
plus an inline section-from-retraction step:

1. `exists_finite_affine_refinement_in_sieve`: a pro-etale covering sieve `S` of `Spec A`
   contains a *finite, standard, affine* pro-etale covering `{Spec Bⱼ → Spec A}` (jointly
   surjective, each weakly etale, each arrow in `S`).  This is the Tag-`098D` reduction,
   obtained from `Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition`
   (which extracts an actual covering presieve `R ≤ S.arrows`) together with
   `QuasiCompactCover.exists_hom` (which refines a QC cover of a compact space to a finite
   affine one).
2. `product_isFaithfullyFlat_weaklyEtale`: the finite product algebra `B = ∏ⱼ Bⱼ` of a
   jointly-surjective weakly-etale family is itself faithfully flat and weakly etale over
   `A`.
3. w-contractibility of `A` applied to `B = ∏ⱼ Bⱼ` gives a retraction, hence a section
   `s : Spec A → Spec B`.
4. `clopen_decomposition_from_section`: pulling back the clopen pieces `Spec Bⱼ` of
   `Spec B = ∐ⱼ Spec Bⱼ` along `s` produces the Zariski clopen decomposition
   `Spec A = ∐ⱼ Uⱼ`, each `Uⱼ → Spec A` factoring through `Spec Bⱼ → Spec A ∈ S`.
-/

/-- **(1) ⇒ (3), step 1 (Tag `098D` reduction).**  A pro-etale covering sieve `S` of
`T = Spec A` contains a *finite, standard, affine* pro-etale covering: there is a finite
family of `A`-algebras `Bⱼ`, each weakly etale, with `{Spec Bⱼ → Spec A}` jointly surjective
and each arrow `specMapOf A (B j) ∈ S`.

The proof: `proetaleTopology = proetalePrecoverage.toGrothendieck`; apply
`CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition` (instances
`IsStableUnderComposition`, `IsStableUnderBaseChange`, `HasPullbacks`, `HasIsos` all hold for
`Scheme.proetalePrecoverage`) to extract a covering presieve `R ∈ proetalePrecoverage.coverings
(specOf A)`
with `R ≤ S.arrows`.  `R` is a `Scheme.Cover (precoverage @WeaklyEtale)`; `specOf A` is a
`CompactSpace`, so `AlgebraicGeometry.QuasiCompactCover.exists_hom` refines it to a *finite*
`Scheme.AffineCover @WeaklyEtale (specOf A)` whose arrows are weakly etale open immersions and
factor through `R ≤ S`.  Read off the affine pieces `Bⱼ := (𝒱.X j)` and their algebra maps. -/
lemma exists_finite_affine_refinement_in_sieve (A : Type u) [CommRing A]
    (S : Sieve (specOf A)) (hS : S ∈ Scheme.proetaleTopology.{u}.sieves (specOf A)) :
    ∃ (n : ℕ) (B : Fin n → Type u) (_ : ∀ j, CommRing (B j)) (_ : ∀ j, Algebra A (B j)),
      (∀ j, IsWeaklyEtale A (B j)) ∧
      (∀ x : (specOf A), ∃ j, x ∈ Set.range (specMapOf A (B j)).base) ∧
      (∀ j, S.arrows (specMapOf A (B j))) := by
  -- Step 1: extract a covering presieve `R ≤ S.arrows` from the topology membership.
  have hmem : S ∈ Scheme.proetalePrecoverage.{u}.toGrothendieck (specOf A) := hS
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hmem
  obtain ⟨R, hR, hRS⟩ := hmem
  -- `R` is a quasi-compact `@WeaklyEtale`-cover of `specOf A`.
  rw [show Scheme.proetalePrecoverage.{u} = Scheme.propQCPrecoverage @WeaklyEtale from rfl,
    Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover] at hR
  obtain ⟨𝒰, hQCC, hRpre⟩ := hR
  -- Step 2: `specOf A` is a compact space, refine to a finite affine cover.
  have : IsAffine (specOf A) := by unfold specOf; infer_instance
  have : CompactSpace (specOf A) := by infer_instance
  have : QuasiCompactCover 𝒰.toPreZeroHypercover := hQCC
  obtain ⟨𝒱, fhom, hfin, hoi⟩ := QuasiCompactCover.exists_hom 𝒰
  have : Finite 𝒱.I₀ := hfin
  -- reindex by `Fin n`
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin 𝒱.I₀
  -- the affine pieces, as `Type u` rings, with their `A`-algebra structures.
  set B : Fin n → Type u := fun j => (𝒱.X (e.symm j)).carrier with hB
  let cr : ∀ j, CommRing (B j) := fun j => inferInstance
  let alg : ∀ j, Algebra A (B j) := fun j =>
    (Spec.preimage (R := CommRingCat.of A) (S := 𝒱.X (e.symm j)) (𝒱.f (e.symm j))).hom.toAlgebra
  -- the key equality: `specMapOf A (B j) = 𝒱.f (e.symm j)`.
  have heq : ∀ j, specMapOf A (B j) = 𝒱.f (e.symm j) := by
    intro j
    show Scheme.Spec.map (CommRingCat.ofHom (algebraMap A (B j))).op = 𝒱.f (e.symm j)
    set φ : CommRingCat.of A ⟶ 𝒱.X (e.symm j) :=
      Spec.preimage (R := CommRingCat.of A) (S := 𝒱.X (e.symm j)) (𝒱.f (e.symm j)) with hφ
    have halg : algebraMap A (B j) = φ.hom := rfl
    rw [halg]
    have hof : CommRingCat.ofHom φ.hom = φ := rfl
    rw [hof]
    show Spec.map φ = 𝒱.f (e.symm j)
    exact Spec.map_preimage (𝒱.f (e.symm j))
  refine ⟨n, B, cr, alg, ?_, ?_, ?_⟩
  · -- weak etaleness: `specMapOf A (B j) = 𝒱.f (e.symm j)`, which is `@WeaklyEtale`.
    intro j
    refine isWeaklyEtale_of_weaklyEtale_specMapOf ?_
    rw [heq j]; exact 𝒱.map_prop (e.symm j)
  · -- joint surjectivity: use `𝒱.covers`.
    intro x
    refine ⟨e (𝒱.idx x), ?_⟩
    -- transport the goal's morphism along `heq`.
    have hrange : Set.range (specMapOf A (B (e (𝒱.idx x)))).base
        = Set.range (𝒱.f (e.symm (e (𝒱.idx x)))).base :=
      congrArg (fun m => Set.range m.base) (heq (e (𝒱.idx x)))
    rw [hrange]
    -- `𝒱.covers x` gives membership in `Set.range (𝒱.f (𝒱.idx x)).base`; align the index.
    have hcov := 𝒱.covers x
    rwa [Equiv.symm_apply_apply]
  · -- sieve membership: `𝒱.f (e.symm j) = fhom.h₀ _ ≫ 𝒰.f (fhom.s₀ _)`, and `𝒰.f _ ∈ R ≤ S`.
    intro j
    rw [heq j]
    have hw := fhom.w₀ (e.symm j)
    -- hw : fhom.h₀ (e.symm j) ≫ 𝒰.f (fhom.s₀ (e.symm j)) = 𝒱.cover.f (e.symm j) = 𝒱.f (e.symm j)
    have hUmem : R (𝒰.f (fhom.s₀ (e.symm j))) := by
      rw [hRpre]; exact Presieve.ofArrows.mk _
    have hSmem : S.arrows (𝒰.f (fhom.s₀ (e.symm j))) :=
      @hRS _ (𝒰.f (fhom.s₀ (e.symm j))) hUmem
    have := S.downward_closed hSmem (fhom.h₀ (e.symm j))
    rwa [hw] at this

/-- The kernel of the `j`-th projection `∏ Bⱼ → Bⱼ` is generated by `1 - Pi.single j 1`. -/
private lemma ker_evalRingHom_eq_span {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)]
    [DecidableEq ι] (j : ι) :
    RingHom.ker (Pi.evalRingHom B j) = Ideal.span {1 - Pi.single j (1 : B j)} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker, Pi.evalRingHom_apply] at hx
    rw [Ideal.mem_span_singleton]
    refine ⟨x, ?_⟩
    ext k
    by_cases h : k = j
    · subst h
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.single_eq_same, sub_self, zero_mul,
        hx]
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.single_eq_of_ne h, sub_zero, one_mul]
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, RingHom.mem_ker, Pi.evalRingHom_apply]
    simp

/-- `Spec` of the `j`-th projection `∏ Bⱼ → Bⱼ` is an open immersion. -/
private lemma isOpenImmersion_spec_evalRingHom {ι : Type} (B : ι → Type u)
    [∀ i, CommRing (B i)] (j : ι) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom B j))) := by
  classical
  rw [AlgebraicGeometry.isOpenImmersion_SpecMap_iff_of_surjective
    (CommRingCat.ofHom (Pi.evalRingHom B j))
    (by change Function.Surjective (Pi.evalRingHom B j); exact RingHomSurjective.is_surjective)]
  refine ⟨1 - Pi.single j (1 : B j), ?_, ker_evalRingHom_eq_span B j⟩
  have hidem : IsIdempotentElem (Pi.single j (1 : B j)) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  exact hidem.one_sub

/-- The range of `Spec f` on underlying spaces is the range of `PrimeSpectrum.comap f`. -/
private lemma range_spec_map_eq_range_comap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    Set.range (Scheme.Spec.map (CommRingCat.ofHom f).op).base
      = Set.range (PrimeSpectrum.comap f) := by
  ext x
  constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, by rw [← hy]; rfl⟩

/-- The images of the projections `Spec(πⱼ)` cover `Spec(∏ Bⱼ)`. -/
private lemma iUnion_range_comap_pi_evalRingHom {ι : Type*} (B : ι → Type*)
    [∀ i, CommRing (B i)] [Finite ι] :
    (⋃ j, Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) = Set.univ := by
  have h := PrimeSpectrum.iUnion_range_comap_comp_evalRingHom (RingHom.id (∀ i, B i))
  simp only [RingHom.comp_id] at h
  rw [h, PrimeSpectrum.comap_id]
  exact Set.range_id

/-- The projection `∏ Bⱼ → Bⱼ` is a retraction of the structure map `A → ∏ Bⱼ` composed
with `A → Bⱼ`. -/
private lemma evalRingHom_comp_algebraMap (A : Type u) [CommRing A] {ι : Type*}
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] (j : ι) :
    (Pi.evalRingHom B j).comp (algebraMap A (∀ i, B i)) = algebraMap A (B j) := by
  ext a; simp [Pi.evalRingHom_apply]

/-- `Spec` of the `j`-th projection followed by the structure map of `∏ Bⱼ` is the structure
map of `Bⱼ`. -/
private lemma spec_evalRingHom_comp_specMapOf (A : Type u) [CommRing A] {ι : Type}
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] (j : ι) :
    Scheme.Spec.map (CommRingCat.ofHom (Pi.evalRingHom B j)).op ≫ specMapOf A (∀ i, B i)
      = specMapOf A (B j) := by
  unfold specMapOf
  rw [← Scheme.Spec.map_comp, ← op_comp, ← CommRingCat.ofHom_comp,
    evalRingHom_comp_algebraMap]

/-- **(1) ⇒ (3), step 2.**  The finite product `B = ∏ⱼ Bⱼ` of a jointly-surjective
weakly-etale family `{A → Bⱼ}` is faithfully flat and weakly etale over `A`.

Flatness of a finite product follows from each `Bⱼ` flat (`Module.Flat` is
closed under finite products / `Pi`).  Weak etaleness: the multiplication map of the product
is the product of multiplication maps, so its flatness reduces to each `lmul'` being flat.
Faithful flatness: a flat module is faithfully flat iff `Spec` is surjective; the family is
jointly surjective on `Spec A`, and `Spec(∏ Bⱼ) = ∐ Spec Bⱼ` surjects onto `Spec A`, so
`B = ∏ Bⱼ` is faithfully flat. -/
@[sga "3 VIB 11.9.1" "partial"]
lemma product_isFaithfullyFlat_weaklyEtale (A : Type u) [CommRing A]
    (n : ℕ) (B : Fin n → Type u) [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)]
    (hwe : ∀ j, IsWeaklyEtale A (B j))
    (hsurj : ∀ x : (specOf A), ∃ j, x ∈ Set.range (specMapOf A (B j)).base) :
    IsWeaklyEtale A (∀ j, B j) ∧ Module.FaithfullyFlat A (∀ j, B j) := by
  classical
  set C : Type u := ∀ j, B j with hC
  -- The projection maps `Spec (B j) → Spec C`, induced by `Pi.evalRingHom`.
  set proj : (j : Fin n) → specOf (B j) ⟶ specOf C := fun j =>
    Scheme.Spec.map (CommRingCat.ofHom (Pi.evalRingHom B j)).op with hproj
  -- `proj j` followed by the structure map of `C` is the structure map of `B j`.
  have hprojcomp : ∀ j, proj j ≫ specMapOf A C = specMapOf A (B j) :=
    spec_evalRingHom_comp_specMapOf A B
  -- `proj j` is an open immersion (kernel of the projection is generated by an idempotent).
  have hoi : ∀ j, IsOpenImmersion (proj j) := isOpenImmersion_spec_evalRingHom B
  -- The `proj j` are jointly surjective onto `Spec C`.
  have hcoverC : ∀ x : (specOf C), ∃ j y, (proj j) y = x := by
    intro x
    have hx : x ∈ (⋃ j, Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) := by
      rw [iUnion_range_comap_pi_evalRingHom]; trivial
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    rw [← range_spec_map_eq_range_comap] at hj
    obtain ⟨y, hy⟩ := hj
    exact ⟨j, y, hy⟩
  -- Assemble the open cover of `Spec C` by the clopen pieces `Spec (B j)`.
  set 𝒰 : (specOf C).OpenCover := Scheme.Cover.mkOfCovers (Fin n) (fun j => specOf (B j)) proj
    hcoverC (fun j => hoi j) with h𝒰
  have hf𝒰 : ∀ j, 𝒰.f j = proj j := fun j => rfl
  -- The structure map of `C` is weakly etale, since `@WeaklyEtale` is local at the source.
  have hweC : AlgebraicGeometry.WeaklyEtale (specMapOf A C) := by
    apply IsZariskiLocalAtSource.of_openCover 𝒰
    intro i
    rw [hf𝒰 i, hprojcomp i]
    exact weaklyEtale_specMapOf_of_isWeaklyEtale (hwe i)
  -- Read off `Module.Flat A C` and flatness of `lmul'` from `hweC`.
  obtain ⟨hMflatC, hlmulC⟩ := isWeaklyEtale_of_weaklyEtale_specMapOf hweC
  -- Faithful flatness: flat + surjectivity of `Spec C → Spec A` (from joint surjectivity).
  have hsurjC : Function.Surjective (PrimeSpectrum.comap (algebraMap A C)) := by
    intro p
    obtain ⟨j, q, hq⟩ := hsurj p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom B j) q, ?_⟩
    have hbase : (specMapOf A (B j)).base q = PrimeSpectrum.comap (algebraMap A (B j)) q := by
      show (Spec.map (CommRingCat.ofHom (algebraMap A (B j)))) q
        = PrimeSpectrum.comap (algebraMap A (B j)) q
      rw [Spec.map_apply]; rfl
    rw [← PrimeSpectrum.comap_comp_apply, evalRingHom_comp_algebraMap, ← hbase, hq]
  have hFFC : Module.FaithfullyFlat A C :=
    @Module.FaithfullyFlat.of_comap_surjective A C _ _ _ hMflatC hsurjC
  exact ⟨⟨hMflatC, hlmulC⟩, hFFC⟩

/-! ### Helper lemmas for `clopen_decomposition_from_section`

The clopen pieces of `Spec(∏ⱼ Bⱼ)` are the basic opens of the idempotents `Pi.single j 1`.
We record the algebraic and topological facts about the projection maps
`πⱼ : ∏ Bⱼ → Bⱼ` (`Pi.evalRingHom B j`) that the geometric argument needs. -/

/-- The `j`-th component idempotent `Pi.single j 1` of a finite product ring is idempotent. -/
theorem single_isIdempotent {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [DecidableEq ι]
    (j : ι) : IsIdempotentElem (Pi.single j (1 : B j)) := by
  rw [IsIdempotentElem, ← Pi.single_mul, mul_one]

/-- The kernel of the `j`-th projection `∏ Bⱼ → Bⱼ` is generated by the complementary
idempotent `1 - Pi.single j 1`. -/
theorem ker_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [DecidableEq ι]
    (j : ι) : RingHom.ker (Pi.evalRingHom B j) = Ideal.span {1 - Pi.single j (1 : B j)} :=
  ker_evalRingHom_eq_span B j

/-- The image of `Spec(πⱼ)` (the range of `comap` of the `j`-th projection) is the clopen basic
open of the idempotent `Pi.single j 1`. -/
theorem range_comap_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)] [DecidableEq ι]
    (j : ι) : Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j)) =
      (PrimeSpectrum.basicOpen (Pi.single j (1 : B j)) : Set _) := by
  rw [range_comap_of_surjective _ _ (RingHomSurjective.is_surjective),
    PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem _ (single_isIdempotent B j),
    ker_evalRingHom, PrimeSpectrum.zeroLocus_span]

/-- The image of the `j`-th projection's `Spec` is clopen. -/
theorem isClopen_range_comap_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)]
    (j : ι) :
    IsClopen (Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) := by
  classical
  rw [range_comap_evalRingHom]
  exact PrimeSpectrum.isClopen_iff.mpr ⟨_, single_isIdempotent B j, rfl⟩

/-- The images of the projections `Spec(πⱼ)` cover `Spec(∏ Bⱼ)`. -/
theorem iUnion_range_comap_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)]
    [Finite ι] :
    (⋃ j, Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) = Set.univ :=
  iUnion_range_comap_pi_evalRingHom B

/-- The images of distinct projections `Spec(πᵢ)`, `Spec(πⱼ)` are disjoint. -/
theorem disjoint_range_comap_evalRingHom {ι : Type*} (B : ι → Type*) [∀ i, CommRing (B i)]
    (i j : ι) (hij : i ≠ j) :
    Disjoint (Set.range (PrimeSpectrum.comap (Pi.evalRingHom B i)))
      (Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) := by
  classical
  rw [range_comap_evalRingHom, range_comap_evalRingHom, Set.disjoint_iff]
  intro p hp
  simp only [Set.mem_inter_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hp
  obtain ⟨hi, hj⟩ := hp
  have hzero : Pi.single i (1 : B i) * Pi.single j (1 : B j) = 0 := by
    ext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.mul_apply, Pi.single_eq_of_ne hij, mul_zero, Pi.zero_apply]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hk, zero_mul, Pi.zero_apply]
  have hp' : p.asIdeal.IsPrime := p.isPrime
  rcases hp'.mem_or_mem (show Pi.single i (1 : B i) * Pi.single j (1 : B j) ∈ p.asIdeal by
    rw [hzero]; exact p.asIdeal.zero_mem) with h | h
  · exact (hi h).elim
  · exact (hj h).elim

/-- The clopen-piece inclusion `Spec Bⱼ → Spec(∏ Bⱼ)` induced by the `j`-th projection. -/
noncomputable def projSpecMap (n : ℕ) (B : Fin n → Type u) [∀ j, CommRing (B j)] (j : Fin n) :
    specOf (B j) ⟶ specOf (∀ i, B i) :=
  Scheme.Spec.map (CommRingCat.ofHom (Pi.evalRingHom B j)).op

/-- `projSpecMap` composed with the structure map of `∏ Bⱼ` is the structure map of `Bⱼ`. -/
theorem projSpecMap_comp (A : Type u) [CommRing A] (n : ℕ) (B : Fin n → Type u)
    [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)] (j : Fin n) :
    projSpecMap n B j ≫ specMapOf A (∀ i, B i) = specMapOf A (B j) :=
  spec_evalRingHom_comp_specMapOf A B j

/-- The underlying-space range of `projSpecMap` is the range of the projection's `comap`. -/
theorem projSpecMap_range (n : ℕ) (B : Fin n → Type u) [∀ j, CommRing (B j)] (j : Fin n) :
    Set.range (projSpecMap n B j).base
      = Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j)) :=
  range_spec_map_eq_range_comap _

/-- `projSpecMap` is an open immersion (the kernel of the projection is generated by an
idempotent). -/
theorem isOpenImmersion_projSpecMap (n : ℕ) (B : Fin n → Type u) [∀ j, CommRing (B j)]
    (j : Fin n) : IsOpenImmersion (projSpecMap n B j) :=
  isOpenImmersion_spec_evalRingHom B j

/-- **(1) ⇒ (3), step 4.**  Given a section `s : Spec A → Spec B` of the structure map of
`B = ∏ⱼ Bⱼ` (each `A → Bⱼ` an arrow of `S`), pulling back the clopen pieces
`Spec Bⱼ ⊆ Spec B = ∐ⱼ Spec Bⱼ` along `s` produces a Zariski clopen decomposition
`Spec A = ∐ⱼ Uⱼ` refining `S`.

`Spec(∏ⱼ Bⱼ) ≅ ∐ⱼ Spec Bⱼ`, with the pieces clopen via the idempotents `eⱼ` of the
product.  Set `Uⱼ := s⁻¹(Spec Bⱼ)` (pullback / preimage along the section `s`); the `Uⱼ` are
clopen (preimages of clopens under the continuous `s`), pairwise disjoint, and cover `Spec A`
(the `Spec Bⱼ` cover `Spec B` and `s` is a section).  Each open immersion `Uⱼ → Spec A`
factors as `Uⱼ → Spec Bⱼ → Spec A` through `specMapOf A (B j) ∈ S` (the composite of the
restricted section with the clopen-piece inclusion lands on `specMapOf A (B j)` by
`s ≫ structure map = 𝟙`), so `S.arrows (Uⱼ → Spec A)`. -/
lemma clopen_decomposition_from_section (A : Type u) [CommRing A]
    (n : ℕ) (B : Fin n → Type u) [∀ j, CommRing (B j)] [∀ j, Algebra A (B j)]
    (S : Sieve (specOf A)) (harr : ∀ j, S.arrows (specMapOf A (B j)))
    (s : specOf A ⟶ specOf (∀ j, B j))
    (hs : s ≫ specMapOf A (∀ j, B j) = 𝟙 (specOf A)) :
    ∃ (m : ℕ) (U : Fin m → Scheme.{u}) (f : (i : Fin m) → U i ⟶ specOf A),
      IsClopenDecompositionCover U f ∧ ClopenDecompositionRefines U f S := by
  classical
  -- Each clopen-piece inclusion `Spec Bⱼ → Spec(∏ Bⱼ)` is an open immersion.
  have hoi : ∀ j, IsOpenImmersion (projSpecMap n B j) := fun j => isOpenImmersion_projSpecMap n B j
  -- `Uⱼ := s⁻¹(Spec Bⱼ)` as the pullback of the clopen piece along the section `s`, with
  -- open immersion `f j := pullback.fst`.
  set U : Fin n → Scheme.{u} := fun j => pullback s (projSpecMap n B j) with hU
  set f : (j : Fin n) → U j ⟶ specOf A := fun j => pullback.fst s (projSpecMap n B j) with hf
  -- The range of `f j` is the preimage along `s` of the clopen piece.
  have hrange : ∀ j, Set.range (f j).base
      = s.base ⁻¹' Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j)) := by
    intro j
    rw [hf, Scheme.Pullback.range_fst, projSpecMap_range]
  refine ⟨n, U, f, ?_, ?_⟩
  · refine ⟨fun j => ?_, fun j => ?_, fun i j hij => ?_, ?_⟩
    · -- open immersion: base change of the open immersion `projSpecMap`
      exact inferInstance
    · -- clopen: preimage of a clopen under the continuous `s.base`
      rw [hrange]
      exact (isClopen_range_comap_evalRingHom B j).preimage s.base.hom.continuous
    · -- disjoint: preimage of disjoint sets
      rw [hrange, hrange]
      exact (disjoint_range_comap_evalRingHom B i j hij).preimage s.base
    · -- cover: the pieces cover `Spec(∏ Bⱼ)` and `s` is total
      rw [Set.eq_univ_iff_forall]
      intro x
      simp only [Set.mem_iUnion]
      have hx : s.base x ∈ (⋃ j, Set.range (PrimeSpectrum.comap (Pi.evalRingHom B j))) := by
        rw [iUnion_range_comap_evalRingHom]; trivial
      simp only [Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      exact ⟨j, by rw [hrange]; exact hj⟩
  · -- refinement: `f j` factors through `specMapOf A (B j) ∈ S`, and `S` is a sieve.
    intro j
    have hcond : pullback.fst s (projSpecMap n B j) ≫ s
        = pullback.snd s (projSpecMap n B j) ≫ projSpecMap n B j := pullback.condition
    have hfac : f j = pullback.snd s (projSpecMap n B j) ≫ specMapOf A (B j) := by
      rw [hf, ← projSpecMap_comp A n B j, ← Category.assoc, ← hcond, Category.assoc, hs,
        Category.comp_id]
    rw [hfac]
    exact S.downward_closed (harr j) _

/-- **(1) ⇒ (3)** (Stacks Tag `098F`, Lemma 61.13.1, forward direction).
If `A` is w-contractible then every pro-etale covering of `T = Spec A` has a Zariski
clopen-decomposition refinement. -/
lemma everyProetaleCoverHasZariskiRefinement_of_wContractible (A : Type u) [CommRing A]
    (h1 : IsWContractible.{u, u} A) :
    EveryProetaleCoverHasZariskiRefinement (specOf A) := by
  intro S hS
  -- Step 1: extract a finite standard affine pro-etale covering inside `S` (Tag `098D`).
  obtain ⟨n, B, _, _, hwe, hsurj, harr⟩ := exists_finite_affine_refinement_in_sieve A S hS
  -- Step 2: the product algebra `∏ⱼ Bⱼ` is faithfully flat weakly etale over `A`.
  obtain ⟨hweB, hffB⟩ := product_isFaithfullyFlat_weaklyEtale A n B hwe hsurj
  -- Step 3: w-contractibility gives a retraction, hence a section `s : Spec A → Spec B`.
  obtain ⟨σ⟩ := h1 (∀ j, B j) hweB hffB
  -- Turn the retraction `σ : (∀ j, B j) →ₐ[A] A` into a section of `specMapOf`.
  set s : specOf A ⟶ specOf (∀ j, B j) :=
    Scheme.Spec.map (CommRingCat.ofHom σ.toRingHom).op with hsdef
  have hs : s ≫ specMapOf A (∀ j, B j) = 𝟙 (specOf A) := by
    rw [hsdef, specMapOf, ← Scheme.Spec.map_comp, ← op_comp, ← CommRingCat.ofHom_comp]
    have hcomp : σ.toRingHom.comp (algebraMap A (∀ j, B j)) = RingHom.id A := by
      ext a; simp
    rw [hcomp]
    rw [CommRingCat.ofHom_id, op_id, Scheme.Spec.map_id]
    rfl
  -- Step 4: pull back the clopen pieces along `s` to get the Zariski refinement.
  exact clopen_decomposition_from_section A n B S harr s hs

/-- **Main theorem (Stacks Tag `098H`, Lemma 61.13.2).**
For a ring `A` with `T = Spec A`, w-contractibility of `A` (with the algebra `B` ranging in
the same universe as `A`), weak contractibility of the object `T` in the big pro-etale site,
and the existence of Zariski clopen-decomposition refinements of all pro-etale coverings of
`T` are equivalent. -/
theorem main_theorem (A : Type u) [CommRing A] :
    [IsWContractible.{u, u} A,
      IsWeaklyContractibleObj (specOf A),
      EveryProetaleCoverHasZariskiRefinement (specOf A)].TFAE := by
  -- We establish the three-way equivalence by proving the implications
  --   (1) → (3),  (3) → (1),  (3) → (2),  (2) → (1),
  -- which together give (1) ⇔ (3), (3) ⇒ (2) and (2) ⇒ (1), and hence the full TFAE.
  -- This follows the standard Stacks-project proof (Tag `098H`); the geometric and
  -- algebraic content sits in the four implication lemmas above.
  tfae_have h13 : 1 → 3 := fun h1 =>
    everyProetaleCoverHasZariskiRefinement_of_wContractible A h1
  tfae_have h31 : 3 → 1 := isWContractible_of_zariskiRefinement A
  tfae_have h32 : 3 → 2 := isWeaklyContractibleObj_of_zariskiRefinement A
  tfae_have h21 : 2 → 1 := by
    intro h2 B _ _ hwe hff
    -- (2) ⇒ (1).  Direct argument (affine case): for an arbitrary faithfully flat weakly
    -- etale `A → B`, the single map `Spec B → Spec A` is a pro-etale covering, so
    -- `h_{Spec B} → h_{Spec A}` is a locally surjective morphism of sheaves; weak
    -- contractibility of `T = Spec A` lifts `𝟙 T` to a section `s : T → Spec B`, which
    -- corresponds (via fully faithful `Spec`) to an `A`-algebra retraction `B →ₐ[A] A`.
    -- This avoids constructing the Stacks-`0983` w-contractible cover `D`.
    -- The three steps are the standalone lemmas
    --   `proetaleCoveringSieve_of_ffWeaklyEtale`,
    --   `exists_section_of_weaklyContractibleObj`,
    --   `hasRetraction_of_section`.
    obtain ⟨s, hs⟩ := exists_section_of_weaklyContractibleObj A B h2
      (proetaleCoveringSieve_of_ffWeaklyEtale A B hwe hff)
    exact hasRetraction_of_section A B s hs
  tfae_finish

end ProetaleWContractible
