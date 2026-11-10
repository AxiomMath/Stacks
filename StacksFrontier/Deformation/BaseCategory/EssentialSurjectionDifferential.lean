module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.DerivationSplitting
public import StacksFrontier.Deformation.BaseCategory.JacobiZariskiFunctoriality

/-!
# Essential surjections of `𝒞_Λ` detected on the image of the differential

Let `f : B → A` be a morphism of the base category `𝒞_Λ`. Each object `A` of `𝒞_Λ` presents its
residue field `k` over `Λ`, with conormal module `𝔪_A/𝔪_A²`, differential
`d_A : 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` and the four-term exact sequence of [Stacks, Tag 06S7]; `f`
induces a morphism of those presentations and hence the ladder of [Stacks, Tag 06S8]. This file
reads the surjectivity of `f` off that ladder: `f` is surjective exactly when
`Im(d_B) → Im(d_A)` is surjective, and exactly when `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is
surjective. This is part (1) of [Stacks, Tag 06H0].

Part (2) of that tag replaces "surjective" by "isomorphism" on the right and "surjection" by
"essential surjection" on the left; it is proved here in both directions. Part (3) replaces the
right-hand condition by the relative cotangent space `𝔪/(𝔪_Λ · + 𝔪²)`, which agrees with
`Im(d)` when `k` is separable over the image of `Λ` by [Stacks, Tag 06S9]. Part (4), the
characterization of nonessential small extensions by the existence of a section, is
`Deformation.not_isEssentialSurjection_iff_exists_section` and is proved elsewhere.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.residueExt`: an object of `𝒞_Λ`, viewed as a presentation of
  `k` over `Λ`.
* `Deformation.ArtinianLocalAlgCat.residueExtHom`: the morphism of presentations induced by a
  morphism of `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.h1ToCotangent`: the arrow `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A²` opening
  the four-term sequence, read on the conormal module of `residueExt`.
* `Deformation.ArtinianLocalAlgCat.imageDMap`: the map `Im(d_B) → Im(d_A)` induced by a
  morphism of `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.derivationKerObj` and
  `Deformation.ArtinianLocalAlgCat.derivationKerHom`: the subalgebra `{b ∈ B | D b = 0}` cut out
  by a `Λ`-derivation `D : B → k` which takes the value `1` on the maximal ideal, as an object
  of `𝒞_Λ` together with its inclusion into `B`.

## Main results

* `Deformation.ArtinianLocalAlgCat.surjective_iff_imageDMap_surjective`: **Stacks 06H0 (1)(a)**,
  `f` is surjective exactly when `Im(d_B) → Im(d_A)` is surjective.
* `Deformation.ArtinianLocalAlgCat.surjective_iff_cotangentSpaceMap_residueExtHom_surjective`:
  **Stacks 06H0 (1)(b)**, `f` is surjective exactly when
  `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is surjective.
* `Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_cotangentSpaceMap_bijective`:
  **Stacks 06H0 (2)**, conditions (a) and (c): `f` is an essential surjection exactly when
  `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is an isomorphism.
* `Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_imageDMap_bijective` and
  `Deformation.ArtinianLocalAlgCat.imageDMap_bijective_iff_cotangentSpaceMap_bijective`:
  **Stacks 06H0 (2)**, the remaining pairs of conditions.
* `Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_relativeCotangentSpaceMap_bijective`:
  **Stacks 06H0 (3)**, the separable case.
* `Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_derivation`: the key step of
  part (2), that a `Λ`-derivation `B → k` taking the value `1` on an element of `𝔪_B` whose
  image lies in `𝔪_A²` obstructs essential surjectivity.
* `Deformation.ArtinianLocalAlgCat.isArtinianRing_of_add_maximalIdeal`: a `Λ`-subalgebra of an
  object of `𝒞_Λ` which together with the maximal ideal spans it is again Artinian.
* `Deformation.ArtinianLocalAlgCat.surjective_hom_iff_surjective_cotangentMap` and
  `Deformation.ArtinianLocalAlgCat.surjective_hom_iff_exists_sub_mem_sq`: the criterion of
  [Stacks, Tag 06S3] restated on the conormal module of `residueExt`, and in element form.

## Implementation notes

An object `A` of `𝒞_Λ` carries no `Λ`-algebra surjection onto `k` on the nose: it carries an
isomorphism `residueEquiv : ResidueField A ≃ₐ[Λ] k`. The instances `residueAlgebra` and
`residueIsScalarTower` install the composite `A → ResidueField A → k` as the algebra structure,
which makes `A` a presentation of `k` over `Λ` with kernel `𝔪_A`
(`residueExt_ker`). A *morphism* of `𝒞_Λ` supplies the remaining data of the 06S8 ladder — an
algebra structure `Algebra B A` and the scalar towers over it — but those depend on the morphism
and so cannot be instances; they are introduced locally inside `residueExtHom` and inside the
proofs of the three squares, after which nothing downstream mentions them. In particular the
statements below carry no `let`-bound instances: the two cotangent spaces and the two conormal
modules depend only on the objects.

The tensor factors are ordered as in Mathlib, so the cotangent space of `A` is `k ⊗_A Ω_{A/Λ}`
rather than the `Ω_{A/Λ} ⊗_A k` of the source, and `Im(d_A)` is the submodule
`LinearMap.range (residueExt A).cotangentComplex` of it.

`h1ToCotangent` is recorded as a bare function rather than as a linear map: only its image is
ever used, and the composite linear map would have to reconcile the module structure that
`Algebra.Extension.Cotangent` carries over `(residueExt A).Ring` with the one that
`Ideal.Cotangent` carries over `A`.

The construction behind part (2)(a) ⟹ (2)(c) is simpler than the source's. The source splits
`Ω_{B/Λ} ⊗_B k = Ω_{A/Λ} ⊗_A k ⊕ K` and uses the `K`-valued projection of `d`; here a single
`k`-linear functional `λ` with `λ v = 1` on one nonzero `v` of the kernel is enough, and
`D b = λ(1 ⊗ d b)` is an honest `Λ`-derivation into `k`, so the subalgebra it cuts out is
`Deformation.DerivationSplitting.kernelSubalgebra`. Neither part (1) nor `Im(d)` enters that
argument: `exists_cotangentComplex_mk_eq` produces `t ∈ 𝔪_B` with `D t = 1` and `f t ∈ 𝔪_A²`
directly from the 06S8 ladder, and then `𝔪_C/𝔪_C² → 𝔪_A/𝔪_A²` is surjective by correcting a
lift `b` to `b - u t`.

The source asserts without argument that the subalgebra `C = {b ∈ B | D b = 0}` is an object of
`𝒞_Λ` once `C → k` is surjective. Artinianness of a subring is not automatic and Mathlib has no
Eakin–Nagata theorem, so `isArtinianRing_of_add_maximalIdeal` proves it by hand for a subalgebra
`C` with `C + 𝔪_B = B`: the ideals `(N ∩ 𝔪_B^i) + 𝔪_B^{i+1}` of `subalgebraFiltrationIdeal`
embed the lattice of `C`-submodules of `B` strictly monotonically into a finite power of the
lattice of ideals of `B`.

## References

* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 06S3](https://stacks.math.columbia.edu/tag/06S3)
* [Stacks Project, Tag 06S7](https://stacks.math.columbia.edu/tag/06S7)
* [Stacks Project, Tag 06S8](https://stacks.math.columbia.edu/tag/06S8)
* [Stacks Project, Tag 06S9](https://stacks.math.columbia.edu/tag/06S9)
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Objects and morphisms of `𝒞_Λ` as presentations of the residue field -/

/-- An object of `𝒞_Λ` is an algebra over its own residue field `k`, through the composite of
the residue map with the chosen identification `ResidueField A ≃ₐ[Λ] k`. -/
noncomputable instance residueAlgebra (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : Algebra A k :=
  (A.residueEquiv.toAlgHom.toRingHom.comp (residue A)).toAlgebra

/-- The structure map of `residueAlgebra` is the residue map followed by the chosen
identification of the residue field with `k`. -/
theorem algebraMap_eq_residue (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (a : A) :
    algebraMap A k a = A.residueEquiv (residue A a) := rfl

/-- The residue map of an object of `𝒞_Λ` is a map of `Λ`-algebras. -/
instance residueIsScalarTower (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    IsScalarTower Λ A k :=
  .of_algebraMap_eq fun x => by
    rw [algebraMap_eq_residue, ← A.residueEquiv.commutes x]; rfl

/-- The residue map of an object of `𝒞_Λ` is surjective. -/
theorem algebraMap_residue_surjective (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Function.Surjective (algebraMap A k) :=
  A.residueEquiv.surjective.comp residue_surjective

/-- An object of `𝒞_Λ`, viewed as a presentation of the residue field `k` over `Λ`. Its
conormal module is `𝔪_A/𝔪_A²` and its cotangent space is `k ⊗_A Ω_{A/Λ}`. -/
noncomputable abbrev residueExt (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Algebra.Extension.{v} Λ k :=
  residueExtension Λ (algebraMap_residue_surjective A)

/-- The kernel of the presentation `residueExt A` is the maximal ideal of `A`. -/
theorem residueExt_ker (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    (residueExt A).ker = maximalIdeal A :=
  residueExtension_ker_eq_maximalIdeal Λ _

variable {B A : ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The morphism of presentations of `k` over `Λ` induced by a morphism of `𝒞_Λ`. -/
noncomputable def residueExtHom (f : B ⟶ A) : (residueExt B).Hom (residueExt A) :=
  letI : Algebra B A := f.hom.toRingHom.toAlgebra
  letI : IsScalarTower Λ B A := .of_algebraMap_eq fun x => (f.hom.commutes x).symm
  letI : IsScalarTower B A k := .of_algebraMap_eq fun b => (f.residue_comm b).symm
  residueExtensionHom (algebraMap_residue_surjective B) (algebraMap_residue_surjective A)

/-- The ring map underlying `residueExtHom f` is the algebra map underlying `f`. -/
theorem residueExtHom_toRingHom_apply (f : B ⟶ A) (x : B) :
    (residueExtHom f).toRingHom x = f.hom x := rfl

/-- A morphism of `𝒞_Λ` carries the kernel of the residue map into the kernel of the residue
map, since it is compatible with the identifications of the residue fields. -/
theorem mem_residueExt_ker_map (f : B ⟶ A) {x : B} (hx : x ∈ (residueExt B).ker) :
    f.hom x ∈ (residueExt A).ker := by
  rw [residueExt_ker] at hx ⊢
  rw [← maximalIdeal_comap (f := f.hom.toRingHom)] at hx
  exact hx

/-- The map `𝔪_B/𝔪_B² → 𝔪_A/𝔪_A²` induced by a morphism of `𝒞_Λ` sends the class of
`x ∈ 𝔪_B` to the class of `f x`. -/
theorem cotangentMap_residueExtHom_mk (f : B ⟶ A) (x : B) (hx : x ∈ (residueExt B).ker) :
    Algebra.Extension.Cotangent.map (residueExtHom f)
        (Algebra.Extension.Cotangent.mk ⟨x, hx⟩) =
      Algebra.Extension.Cotangent.mk ⟨f.hom x, mem_residueExt_ker_map f hx⟩ := by
  rw [Algebra.Extension.Cotangent.map_mk]
  congr 1

/-- **Stacks 06S8**, right square, for a morphism of `𝒞_Λ`: the projection of `k ⊗_B Ω_{B/Λ}`
onto `Ω_{k/Λ}` factors through `k ⊗_A Ω_{A/Λ}` along `f`. -/
theorem toKaehler_comp_cotangentSpaceMap_residueExtHom (f : B ⟶ A) :
    (residueExt A).toKaehler ∘ₗ
        Algebra.Extension.CotangentSpace.map (residueExtHom f) =
      (residueExt B).toKaehler := by
  let _ : Algebra B A := f.hom.toRingHom.toAlgebra
  let _ : IsScalarTower Λ B A := .of_algebraMap_eq fun x => (f.hom.commutes x).symm
  let _ : IsScalarTower B A k := .of_algebraMap_eq fun b => (f.residue_comm b).symm
  exact toKaehler_comp_cotangentSpaceMap _ _

/-- **Stacks 06S8**, right square, in element form. -/
theorem toKaehler_cotangentSpaceMap_residueExtHom (f : B ⟶ A)
    (x : (residueExt B).CotangentSpace) :
    (residueExt A).toKaehler
        (Algebra.Extension.CotangentSpace.map (residueExtHom f) x) =
      (residueExt B).toKaehler x :=
  LinearMap.congr_fun (toKaehler_comp_cotangentSpaceMap_residueExtHom f) x

/-- The arrow `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A²` which opens the four-term exact sequence of
[Stacks, Tag 06S7], read on the conormal module of the presentation `residueExt A`. -/
noncomputable def h1ToCotangent (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Algebra.H1Cotangent Λ k → (residueExt A).Cotangent :=
  fun z => Algebra.Extension.Cotangent.of
    (h1CotangentToCotangent Λ (algebraMap_residue_surjective A) z)

/-- The sequence `H₁(L_{k/Λ}) → 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` is exact: the kernel of `d_A` is the
image of `H₁(L_{k/Λ})`. This is exactness of the four-term sequence of [Stacks, Tag 06S7] at
`𝔪_A/𝔪_A²`, transported to the conormal module of `residueExt A`. -/
theorem exact_h1ToCotangent (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    Function.Exact (h1ToCotangent A) (residueExt A).cotangentComplex := by
  intro x
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := ((exact_h1CotangentToCotangent (Λ := Λ)
      (algebraMap_residue_surjective A)) x.val).mp hx
    exact ⟨z, Algebra.Extension.Cotangent.ext hz⟩
  · rintro ⟨z, rfl⟩
    exact ((exact_h1CotangentToCotangent (Λ := Λ)
      (algebraMap_residue_surjective A)) _).mpr ⟨z, rfl⟩

/-- **Stacks 06S8**, left square, for a morphism of `𝒞_Λ`: pushing a class of `H₁(L_{k/Λ})`
into `𝔪_B/𝔪_B²` and then along `f` gives its image in `𝔪_A/𝔪_A²`. -/
theorem cotangentMap_residueExtHom_h1CotangentToCotangent (f : B ⟶ A)
    (z : Algebra.H1Cotangent Λ k) :
    Algebra.Extension.Cotangent.map (residueExtHom f) (Algebra.Extension.Cotangent.of
        (h1CotangentToCotangent Λ (algebraMap_residue_surjective B) z)) =
      Algebra.Extension.Cotangent.of
        (h1CotangentToCotangent Λ (algebraMap_residue_surjective A) z) := by
  let _ : Algebra B A := f.hom.toRingHom.toAlgebra
  let _ : IsScalarTower Λ B A := .of_algebraMap_eq fun x => (f.hom.commutes x).symm
  let _ : IsScalarTower B A k := .of_algebraMap_eq fun b => (f.residue_comm b).symm
  rw [show residueExtHom f = residueExtensionHom (algebraMap_residue_surjective B)
      (algebraMap_residue_surjective A) from rfl,
    cotangentMap_residueExtensionHom_of]
  congr 1
  exact mapCotangent_h1CotangentToCotangent _ _ z

/-- **Stacks 06S8**, left square, stated for `h1ToCotangent`. -/
theorem cotangentMap_residueExtHom_h1ToCotangent (f : B ⟶ A) (z : Algebra.H1Cotangent Λ k) :
    Algebra.Extension.Cotangent.map (residueExtHom f) (h1ToCotangent B z) =
      h1ToCotangent A z :=
  cotangentMap_residueExtHom_h1CotangentToCotangent f z

/-- The differential `d_A : 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` of the presentation `residueExt A` is the
differential of the four-term sequence of [Stacks, Tag 06S7]. -/
theorem cotangentComplex_residueExt_apply (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (x : (residueExt A).Cotangent) :
    (residueExt A).cotangentComplex x =
      KaehlerDifferential.kerCotangentToTensor Λ A k x.val := rfl

/-- `Ω_{·/Λ} ⊗ k` is functorial on `𝒞_Λ`. -/
theorem cotangentSpaceMap_residueExtHom_comp {C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : C ⟶ B) (f : B ⟶ A) (x : (residueExt C).CotangentSpace) :
    Algebra.Extension.CotangentSpace.map (residueExtHom (g ≫ f)) x =
      Algebra.Extension.CotangentSpace.map (residueExtHom f)
        (Algebra.Extension.CotangentSpace.map (residueExtHom g) x) := by
  have hcomp : residueExtHom (g ≫ f) = (residueExtHom f).comp (residueExtHom g) := by
    ext y
    exact congrArg f.hom (residueExtHom_toRingHom_apply g y)
  rw [hcomp, Algebra.Extension.CotangentSpace.map_comp_apply]

/-! ### Surjectivity on the conormal module -/

/-- The map `𝔪_B/𝔪_B² → 𝔪_A/𝔪_A²` induced by a morphism of `𝒞_Λ` is surjective exactly when
every element of `𝔪_A` is congruent modulo `𝔪_A²` to the image of an element of `𝔪_B`. -/
theorem surjective_cotangentMap_iff_exists_sub_mem_sq (f : B ⟶ A) :
    Function.Surjective (Algebra.Extension.Cotangent.map (residueExtHom f)) ↔
      ∀ a ∈ maximalIdeal A, ∃ b ∈ maximalIdeal B, f.hom b - a ∈ maximalIdeal A ^ 2 := by
  have hB : (residueExt B).ker = maximalIdeal B := residueExt_ker B
  have hA : (residueExt A).ker = maximalIdeal A := residueExt_ker A
  have hA2 : (residueExt A).ker ^ 2 = maximalIdeal A ^ 2 := congrArg (fun I => I ^ 2) hA
  constructor
  · intro hg a ha
    obtain ⟨x, hx⟩ := hg (Algebra.Extension.Cotangent.mk ⟨a, hA.ge ha⟩)
    obtain ⟨⟨b, hb⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    exact ⟨b, hB.le hb, hA2.le ((Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mp
      ((cotangentMap_residueExtHom_mk f b hb).symm.trans hx))⟩
  · intro h z
    obtain ⟨⟨a, ha⟩, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective z
    obtain ⟨b, hb, hd⟩ := h a (hA.le ha)
    refine ⟨Algebra.Extension.Cotangent.mk ⟨b, hB.ge hb⟩,
      (cotangentMap_residueExtHom_mk f b (hB.ge hb)).trans ?_⟩
    exact (Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem _ _).mpr (hA2.ge hd)

/-- The criterion of [Stacks, Tag 06S3] for surjectivity, read on the conormal modules of the
presentations `residueExt B` and `residueExt A`: a morphism of `𝒞_Λ` is surjective exactly when
the map it induces on `𝔪/𝔪²` is surjective. -/
@[stacks 06S3 "conditions (1) and (2), on the conormal module of a presentation"]
theorem surjective_hom_iff_surjective_cotangentMap (f : B ⟶ A) :
    Function.Surjective f.hom ↔
      Function.Surjective (Algebra.Extension.Cotangent.map (residueExtHom f)) := by
  have key : ∀ hle : maximalIdeal B ≤ (maximalIdeal A).comap f.hom,
      Function.Surjective (Ideal.mapCotangent (maximalIdeal B) (maximalIdeal A) f.hom hle) ↔
        ∀ a ∈ maximalIdeal A, ∃ b ∈ maximalIdeal B, f.hom b - a ∈ maximalIdeal A ^ 2 := by
    intro hle
    constructor
    · intro hg a ha
      obtain ⟨x, hx⟩ := hg ((maximalIdeal A).toCotangent ⟨a, ha⟩)
      obtain ⟨⟨b, hb⟩, rfl⟩ := (maximalIdeal B).toCotangent_surjective x
      rw [Ideal.mapCotangent_toCotangent] at hx
      exact ⟨b, hb, (maximalIdeal A).toCotangent_eq.mp hx⟩
    · intro h z
      obtain ⟨⟨a, ha⟩, rfl⟩ := (maximalIdeal A).toCotangent_surjective z
      obtain ⟨b, hb, hd⟩ := h a ha
      refine ⟨(maximalIdeal B).toCotangent ⟨b, hb⟩, ?_⟩
      rw [Ideal.mapCotangent_toCotangent]
      exact (maximalIdeal A).toCotangent_eq.mpr hd
  rw [surjective_iff_cotangentSpaceMap_surjective f]
  exact (key _).trans (surjective_cotangentMap_iff_exists_sub_mem_sq f).symm

/-- The criterion of [Stacks, Tag 06S3] in element form: a morphism of `𝒞_Λ` is surjective
exactly when every element of `𝔪_A` is congruent modulo `𝔪_A²` to the image of an element of
`𝔪_B`. -/
theorem surjective_hom_iff_exists_sub_mem_sq (f : B ⟶ A) :
    Function.Surjective f.hom ↔
      ∀ a ∈ maximalIdeal A, ∃ b ∈ maximalIdeal B, f.hom b - a ∈ maximalIdeal A ^ 2 :=
  (surjective_hom_iff_surjective_cotangentMap f).trans
    (surjective_cotangentMap_iff_exists_sub_mem_sq f)

/-! ### The image of the differential -/

/-- The map `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` carries `Im(d_B)` into `Im(d_A)`: this is the middle
square of [Stacks, Tag 06S8]. -/
theorem cotangentSpaceMap_residueExtHom_mem_range (f : B ⟶ A)
    {x : (residueExt B).CotangentSpace}
    (hx : x ∈ LinearMap.range (residueExt B).cotangentComplex) :
    Algebra.Extension.CotangentSpace.map (residueExtHom f) x ∈
      LinearMap.range (residueExt A).cotangentComplex := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Algebra.Extension.Cotangent.map (residueExtHom f) y,
    (Algebra.Extension.CotangentSpace.map_cotangentComplex (residueExtHom f) y).symm⟩

/-- The map `Im(d_B) → Im(d_A)` induced by a morphism `f : B ⟶ A` of `𝒞_Λ`, the restriction of
`Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` to the images of the two differentials. -/
noncomputable def imageDMap (f : B ⟶ A) :
    LinearMap.range (residueExt B).cotangentComplex →ₗ[k]
      LinearMap.range (residueExt A).cotangentComplex :=
  (Algebra.Extension.CotangentSpace.map (residueExtHom f)).restrict
    fun _ hx => cotangentSpaceMap_residueExtHom_mem_range f hx

/-- `imageDMap f` is a restriction of the map on cotangent spaces. -/
@[simp]
theorem imageDMap_coe (f : B ⟶ A) (x : LinearMap.range (residueExt B).cotangentComplex) :
    (imageDMap f x : (residueExt A).CotangentSpace) =
      Algebra.Extension.CotangentSpace.map (residueExtHom f) x :=
  LinearMap.coe_restrict_apply _ x

/-- `Im(d_A)` is the kernel of the projection `Ω_{A/Λ} ⊗_A k → Ω_{k/Λ}`: this is exactness of the
four-term sequence of [Stacks, Tag 06S7] at `Ω_{A/Λ} ⊗_A k`. -/
theorem range_cotangentComplex_eq_ker_toKaehler (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    LinearMap.range (residueExt A).cotangentComplex =
      LinearMap.ker (residueExt A).toKaehler :=
  (Function.Exact.linearMap_ker_eq
    (Algebra.Extension.exact_cotangentComplex_toKaehler (P := residueExt A))).symm

/-- An element of `Ω_{B/Λ} ⊗_B k` whose image in `Ω_{A/Λ} ⊗_A k` lies in `Im(d_A)` lies in
`Im(d_B)`, since both images are the kernels of the compatible maps to `Ω_{k/Λ}`. -/
private theorem mem_range_cotangentComplex_of_map_mem (f : B ⟶ A)
    {x : (residueExt B).CotangentSpace}
    (hx : Algebra.Extension.CotangentSpace.map (residueExtHom f) x ∈
      LinearMap.range (residueExt A).cotangentComplex) :
    x ∈ LinearMap.range (residueExt B).cotangentComplex := by
  rw [range_cotangentComplex_eq_ker_toKaehler, LinearMap.mem_ker,
    ← toKaehler_cotangentSpaceMap_residueExtHom f]
  rwa [range_cotangentComplex_eq_ker_toKaehler, LinearMap.mem_ker] at hx

/-- `Im(d_B) → Im(d_A)` is surjective exactly when `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is: the two
differentials have the same cokernel `Ω_{k/Λ}`, compatibly with `f`. -/
theorem imageDMap_surjective_iff_cotangentSpaceMap_surjective (f : B ⟶ A) :
    Function.Surjective (imageDMap f) ↔
      Function.Surjective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) := by
  constructor
  · intro h w
    obtain ⟨x, hx⟩ := (residueExt B).toKaehler_surjective ((residueExt A).toKaehler w)
    have hmem : w - Algebra.Extension.CotangentSpace.map (residueExtHom f) x ∈
        LinearMap.range (residueExt A).cotangentComplex := by
      rw [range_cotangentComplex_eq_ker_toKaehler, LinearMap.mem_ker, map_sub,
        toKaehler_cotangentSpaceMap_residueExtHom, hx, sub_self]
    obtain ⟨v, hv⟩ := h ⟨_, hmem⟩
    have hv' : Algebra.Extension.CotangentSpace.map (residueExtHom f) (v : _) =
        w - Algebra.Extension.CotangentSpace.map (residueExtHom f) x := by
      rw [← imageDMap_coe, hv]
    refine ⟨x + v, ?_⟩
    rw [map_add, hv']
    abel
  · intro h w
    obtain ⟨x, hx⟩ := h w
    have hmem := mem_range_cotangentComplex_of_map_mem f (x := x) (by rw [hx]; exact w.2)
    exact ⟨⟨x, hmem⟩, Subtype.ext ((imageDMap_coe f _).trans hx)⟩

/-- `Im(d_B) → Im(d_A)` is injective exactly when `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is: anything
killed by the latter already lies in `Im(d_B)`, because `Im(d_B)` is the kernel of the map to
`Ω_{k/Λ}` and that map factors through `Ω_{A/Λ} ⊗_A k`. -/
theorem imageDMap_injective_iff_cotangentSpaceMap_injective (f : B ⟶ A) :
    Function.Injective (imageDMap f) ↔
      Function.Injective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hmem := mem_range_cotangentComplex_of_map_mem f (x := x) (by rw [hx]; exact zero_mem _)
    have hzero : imageDMap f ⟨x, hmem⟩ = 0 :=
      Subtype.ext ((imageDMap_coe f _).trans hx)
    exact congrArg Subtype.val ((injective_iff_map_eq_zero _).mp h _ hzero)
  · intro h x y hxy
    exact Subtype.ext (h (((imageDMap_coe f x).symm.trans
      (congrArg Subtype.val hxy)).trans (imageDMap_coe f y)))

/-- An element of the kernel of `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is `d_B` of the class of some
`t ∈ 𝔪_B` whose image in `A` lies in `𝔪_A²`. Indeed it lies in `Im(d_B)`, because the two
differentials have the same cokernel `Ω_{k/Λ}`; the class of a preimage `t ∈ 𝔪_B` then maps
into the kernel of `d_A`, which is the image of `H₁(L_{k/Λ})` by the four-term sequence of
[Stacks, Tag 06S7], so that class may be corrected by the image of a class of `H₁(L_{k/Λ})` —
which does not change its value under `d_B`, since `d_B` also kills the image of
`H₁(L_{k/Λ})` — until its image in `𝔪_A/𝔪_A²` vanishes. -/
theorem exists_cotangentComplex_mk_eq (f : B ⟶ A)
    {v : (residueExt B).CotangentSpace}
    (hv : Algebra.Extension.CotangentSpace.map (residueExtHom f) v = 0) :
    ∃ t : B, ∃ ht : t ∈ (residueExt B).ker, f.hom t ∈ maximalIdeal A ^ 2 ∧
      (residueExt B).cotangentComplex (Algebra.Extension.Cotangent.mk ⟨t, ht⟩) = v := by
  obtain ⟨w, hw⟩ := mem_range_cotangentComplex_of_map_mem f (x := v)
    (by rw [hv]; exact zero_mem _)
  have hA0 : (residueExt A).cotangentComplex
      (Algebra.Extension.Cotangent.map (residueExtHom f) w) = 0 := by
    rw [← Algebra.Extension.CotangentSpace.map_cotangentComplex, hw, hv]
  obtain ⟨z, hz⟩ := (exact_h1ToCotangent A _).mp hA0
  obtain ⟨⟨t, htk⟩, hmk⟩ := Algebra.Extension.Cotangent.mk_surjective (w - h1ToCotangent B z)
  refine ⟨t, htk, ?_, ?_⟩
  · have hz0 : Algebra.Extension.Cotangent.mk
        (P := residueExt A) ⟨f.hom t, mem_residueExt_ker_map f htk⟩ = 0 := by
      rw [← cotangentMap_residueExtHom_mk f t htk, hmk, map_sub,
        cotangentMap_residueExtHom_h1ToCotangent, hz, sub_self]
    have h2 : f.hom t ∈ (residueExt A).ker ^ 2 :=
      (Algebra.Extension.Cotangent.mk_eq_zero_iff _).mp hz0
    rwa [residueExt_ker A] at h2
  · rw [hmk, map_sub, hw, (exact_h1ToCotangent B _).mpr ⟨z, rfl⟩, sub_zero]

/-! ### The subobject cut out by a derivation -/

section DerivationKernel

open DerivationSplitting

/-- For a `Λ`-subalgebra `C` of an object `B` of `𝒞_Λ` which together with `𝔪_B` spans `B`, and
for a `C`-submodule `N` of `B`, the submodule `(N ∩ 𝔪_B^i) + 𝔪_B^{i+1}` of `B` is an ideal of
`B`: multiplying by `b ∈ B` is multiplying by an element of `C`, which preserves `N` and
`𝔪_B^i`, plus multiplying by an element of `𝔪_B`, which carries `𝔪_B^i` into `𝔪_B^{i+1}`. -/
def subalgebraFiltrationIdeal {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (C : Subalgebra Λ B)
    (hC : ∀ b : B, ∃ c : C, b - (c : B) ∈ maximalIdeal B) (N : Submodule C B) (i : ℕ) :
    Ideal B where
  carrier := ((N ⊓ (maximalIdeal B ^ i).restrictScalars C) ⊔
    (maximalIdeal B ^ (i + 1)).restrictScalars C : Submodule C B)
  add_mem' hx hy := Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  smul_mem' b x hx := by
    obtain ⟨c, hc⟩ := hC b
    have hle : ((N ⊓ (maximalIdeal B ^ i).restrictScalars C) ⊔
        (maximalIdeal B ^ (i + 1)).restrictScalars C : Submodule C B) ≤
          (maximalIdeal B ^ i).restrictScalars C :=
      sup_le inf_le_right
        (Submodule.restrictScalars_mono _ (Ideal.pow_le_pow_right (Nat.le_succ i)))
    have hxi : x ∈ maximalIdeal B ^ i := hle hx
    have h1 : (c : B) * x ∈ ((N ⊓ (maximalIdeal B ^ i).restrictScalars C) ⊔
        (maximalIdeal B ^ (i + 1)).restrictScalars C : Submodule C B) := by
      have h := Submodule.smul_mem ((N ⊓ (maximalIdeal B ^ i).restrictScalars C) ⊔
        (maximalIdeal B ^ (i + 1)).restrictScalars C : Submodule C B) c hx
      rwa [Algebra.smul_def] at h
    have h2 : (b - (c : B)) * x ∈ maximalIdeal B ^ (i + 1) := by
      rw [pow_succ, mul_comm]
      exact Ideal.mul_mem_mul hc hxi
    rw [smul_eq_mul, show b * x = (c : B) * x + (b - (c : B)) * x by ring]
    exact Submodule.add_mem _ h1 (Submodule.mem_sup_right h2)

/-- Membership in `subalgebraFiltrationIdeal` is membership in the underlying submodule. -/
theorem mem_subalgebraFiltrationIdeal {B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {C : Subalgebra Λ B} {hC : ∀ b : B, ∃ c : C, b - (c : B) ∈ maximalIdeal B}
    {N : Submodule C B} {i : ℕ} {x : B} :
    x ∈ subalgebraFiltrationIdeal C hC N i ↔
      x ∈ ((N ⊓ (maximalIdeal B ^ i).restrictScalars C) ⊔
        (maximalIdeal B ^ (i + 1)).restrictScalars C : Submodule C B) := Iff.rfl

/-- A `Λ`-subalgebra `C` of an object `B` of `𝒞_Λ` which together with `𝔪_B` spans `B` is again
an Artinian ring.

The powers `𝔪_B^i` are `C`-submodules of `B`, and the ideals `(N ∩ 𝔪_B^i) + 𝔪_B^{i+1}` of
`subalgebraFiltrationIdeal` determine a `C`-submodule `N` of `B` among the `C`-submodules below
it: after correcting an element of `N` by an element of the smaller submodule the remainder lies
one step further down the filtration, and the filtration terminates because `𝔪_B` is nilpotent.
So the lattice of `C`-submodules of `B` embeds strictly monotonically into a finite power of the
lattice of ideals of `B`, which is well-founded. Hence `B` is an Artinian `C`-module, and so is
its `C`-submodule `C`. -/
theorem isArtinianRing_of_add_maximalIdeal {B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (C : Subalgebra Λ B) (hC : ∀ b : B, ∃ c : C, b - (c : B) ∈ maximalIdeal B) :
    IsArtinianRing C := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  have hmono : ∀ {N N' : Submodule C B}, N ≤ N' → ∀ i,
      subalgebraFiltrationIdeal C hC N i ≤ subalgebraFiltrationIdeal C hC N' i := by
    intro N N' h i x hx
    rw [mem_subalgebraFiltrationIdeal] at hx ⊢
    exact sup_le_sup (inf_le_inf h le_rfl) le_rfl hx
  have hsep : ∀ {N N' : Submodule C B}, N' ≤ N →
      (∀ i ≤ n, subalgebraFiltrationIdeal C hC N i = subalgebraFiltrationIdeal C hC N' i) →
      N ≤ N' := by
    intro N N' hle h
    have key : ∀ d : ℕ, ∀ x ∈ N, x ∈ maximalIdeal B ^ (n - d) → x ∈ N' := by
      intro d
      induction d with
      | zero =>
        intro x _ hx
        rw [Nat.sub_zero, hn] at hx
        rw [show x = 0 by simpa using hx]
        exact Submodule.zero_mem _
      | succ d ih =>
        intro x hxN hx
        have hmem : x ∈ subalgebraFiltrationIdeal C hC N (n - (d + 1)) := by
          rw [mem_subalgebraFiltrationIdeal]
          exact Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hxN, hx⟩)
        rw [h (n - (d + 1)) (Nat.sub_le _ _), mem_subalgebraFiltrationIdeal] at hmem
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
        have hzN : z ∈ N := by
          have hzx : z = x - y := by
            rw [← hyz]
            abel
          rw [hzx]
          exact Submodule.sub_mem _ hxN (hle (Submodule.mem_inf.mp hy).1)
        have hz' : z ∈ maximalIdeal B ^ (n - d) := Ideal.pow_le_pow_right (by omega) hz
        rw [← hyz]
        exact Submodule.add_mem _ (Submodule.mem_inf.mp hy).1 (ih z hzN hz')
    intro x hx
    exact key n x hx (by simp)
  have hart : IsArtinian C B := by
    refine StrictMono.wellFoundedLT
      (f := fun (N : Submodule C B) (i : Fin (n + 1)) =>
        subalgebraFiltrationIdeal C hC N i) ?_
    intro N N' hlt
    refine lt_of_le_of_ne (fun i => hmono hlt.le i) fun heq => ?_
    exact hlt.not_ge (hsep hlt.le fun i hi => (congrFun heq ⟨i, by omega⟩).symm)
  exact isArtinian_of_injective (Algebra.linearMap C B) fun x y h => Subtype.ext h

variable (q : B →ₐ[Λ] k) (hq : ∀ a : B, B.residueEquiv (residue B a) = q a)
  (D : B →ₗ[Λ] k) (hD : ∀ a b : B, D (a * b) = q a * D b + q b * D a)
  {t : B} (ht : t ∈ maximalIdeal B) (hDt : D t = 1)

include hq ht hDt in
/-- The kernel of a `Λ`-derivation `D : B → k` over the augmentation still surjects onto `k`,
provided `D` takes the value `1` on an element `t` of `𝔪_B`: a lift `x` of a residue is
corrected to `x - s t`, for `s` any lift of `D x`, and multiplying by `t ∈ 𝔪_B` does not change
residues. -/
theorem kernelAug_surjective_of_mem_maximalIdeal :
    Function.Surjective (kernelAug q D hD) := by
  intro c
  have hqt : q t = 0 := (aug_eq_zero_iff q hq t).mpr ht
  obtain ⟨x, hx⟩ := aug_surjective q hq c
  obtain ⟨s, hs⟩ := aug_surjective q hq (D x)
  have hmem : x - s * t ∈ kernelSubalgebra q D hD := by
    rw [mem_kernelSubalgebra, map_sub, hD, hs, hqt, hDt]
    ring
  refine ⟨⟨x - s * t, hmem⟩, ?_⟩
  change q (x - s * t) = c
  rw [map_sub, map_mul, hqt, hx]
  ring

include hq ht hDt in
/-- Every element of `B` differs from an element of the kernel of the derivation by an element
of `𝔪_B`: the kernel still surjects onto the residue field. -/
theorem exists_mem_kernelSubalgebra_sub_mem (b : B) :
    ∃ c : kernelSubalgebra q D hD, b - (c : B) ∈ maximalIdeal B := by
  obtain ⟨c, hc⟩ := kernelAug_surjective_of_mem_maximalIdeal q hq D hD ht hDt (q b)
  refine ⟨c, (aug_eq_zero_iff q hq _).mp ?_⟩
  rw [map_sub, sub_eq_zero]
  exact (show q (c : B) = q b from hc).symm

include hq in
/-- An element of the kernel of a derivation over the augmentation is a unit there exactly when
its residue is nonzero: if it is, then it is a unit of `B`, and the Leibniz rule applied to
`x x⁻¹ = 1` shows that its inverse is again killed by the derivation. -/
theorem aug_ne_zero_iff_isUnit {x : kernelSubalgebra q D hD} :
    q (x : B) ≠ 0 ↔ IsUnit x := by
  constructor
  · intro hx
    have hxB : IsUnit (x : B) := by
      by_contra h
      exact hx ((aug_eq_zero_iff q hq _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
    obtain ⟨u, hu⟩ := hxB
    have hmul : (x : B) * (↑u⁻¹ : B) = 1 := hu ▸ u.mul_inv
    have hDinv : D (↑u⁻¹ : B) = 0 := by
      have h := hD (x : B) (↑u⁻¹ : B)
      rw [hmul, map_one_eq_zero q D hD, x.2, mul_zero, add_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hx
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hDinv⟩, Subtype.ext hmul⟩
  · intro hx hz
    exact (IsLocalRing.mem_maximalIdeal (x : B)).mp ((aug_eq_zero_iff q hq _).mp hz)
      (hx.map (kernelSubalgebra q D hD).val)

include hq in
/-- The kernel of a derivation over the augmentation is a local ring: by
`aug_ne_zero_iff_isUnit` its nonunits are the elements of zero residue, and those are closed
under addition. -/
theorem isLocalRing_kernelSubalgebra : IsLocalRing (kernelSubalgebra q D hD) := by
  have : Nontrivial (kernelSubalgebra q D hD) :=
    (kernelSubalgebra q D hD).toSubsemiring.nontrivial
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff] at ha hb
  have ha' : q (a : B) = 0 :=
    not_ne_iff.mp fun hne => ha ((aug_ne_zero_iff_isUnit q hq D hD).mp hne)
  have hb' : q (b : B) = 0 :=
    not_ne_iff.mp fun hne => hb ((aug_ne_zero_iff_isUnit q hq D hD).mp hne)
  rw [mem_nonunits_iff]
  intro hab
  refine (aug_ne_zero_iff_isUnit q hq D hD).mpr hab ?_
  rw [show ((a + b : kernelSubalgebra q D hD) : B) = (a : B) + (b : B) from rfl, map_add,
    ha', hb', add_zero]

include hq ht hDt in
/-- The kernel of a derivation over the augmentation, as an object of `𝒞_Λ`. Its underlying ring
is the subalgebra `{b ∈ B | D b = 0}`, which is local by `isLocalRing_kernelSubalgebra`,
Artinian by `isArtinianRing_of_add_maximalIdeal`, and surjects onto `k` by
`kernelAug_surjective_of_mem_maximalIdeal`. -/
noncomputable def derivationKerObj : ArtinianLocalAlgCat.{u, v, w} Λ k :=
  letI : IsLocalRing (kernelSubalgebra q D hD) := isLocalRing_kernelSubalgebra q hq D hD
  { carrier := kernelSubalgebra q D hD
    isArtinianRing := isArtinianRing_of_add_maximalIdeal (kernelSubalgebra q D hD)
      (exists_mem_kernelSubalgebra_sub_mem q hq D hD ht hDt)
    residueEquiv := residueEquivOfAugmentation (kernelAug q D hD)
      (kernelAug_surjective_of_mem_maximalIdeal q hq D hD ht hDt) }

include hq ht hDt in
/-- The chosen identification of the residue field of `derivationKerObj` recovers the
augmentation. -/
theorem derivationKerObj_residueEquiv_residue (x : kernelSubalgebra q D hD) :
    (derivationKerObj q hq D hD ht hDt).residueEquiv
        (residue (derivationKerObj q hq D hD ht hDt) x) = q (x : B) := rfl

include hq ht hDt in
/-- The maximal ideal of `derivationKerObj` is the kernel of its augmentation. -/
theorem maximalIdeal_derivationKerObj :
    maximalIdeal (derivationKerObj q hq D hD ht hDt) =
      RingHom.ker (kernelAug q D hD).toRingHom := by
  have : IsLocalRing (kernelSubalgebra q D hD) := isLocalRing_kernelSubalgebra q hq D hD
  exact (IsLocalRing.ker_eq_maximalIdeal (kernelAug q D hD).toRingHom
    (kernelAug_surjective_of_mem_maximalIdeal q hq D hD ht hDt)).symm

include hq ht hDt in
/-- An element of `derivationKerObj` lies in its maximal ideal exactly when it lies in
`𝔪_B`. -/
theorem mem_maximalIdeal_derivationKerObj {x : kernelSubalgebra q D hD} :
    x ∈ maximalIdeal (derivationKerObj q hq D hD ht hDt) ↔ (x : B) ∈ maximalIdeal B := by
  rw [maximalIdeal_derivationKerObj q hq D hD ht hDt]
  exact ⟨fun h => (aug_eq_zero_iff q hq _).mp h, fun h => (aug_eq_zero_iff q hq _).mpr h⟩

include hq ht hDt in
/-- The inclusion of the kernel of a derivation, as a morphism of `𝒞_Λ`. -/
noncomputable def derivationKerHom : derivationKerObj q hq D hD ht hDt ⟶ B where
  hom := (kernelSubalgebra q D hD).val
  isLocal := ⟨fun x hx => (aug_ne_zero_iff_isUnit q hq D hD).mp fun h =>
    (IsLocalRing.mem_maximalIdeal ((kernelSubalgebra q D hD).val x)).mp
      ((aug_eq_zero_iff q hq _).mp h) hx⟩
  residue_comm x := by
    rw [hq]
    rfl

include hq ht hDt in
/-- The inclusion morphism of `derivationKerHom` is the inclusion of the subalgebra. -/
@[simp]
theorem derivationKerHom_hom_apply (x : kernelSubalgebra q D hD) :
    (derivationKerHom q hq D hD ht hDt).hom x = (x : B) := rfl

include hq ht hDt in
/-- The derivation vanishes on the image of `derivationKerHom`. -/
theorem map_derivationKerHom (x : derivationKerObj q hq D hD ht hDt) :
    D ((derivationKerHom q hq D hD ht hDt).hom x) = 0 :=
  (mem_kernelSubalgebra q D hD).mp x.2

include hq hD ht hDt in
/-- **The key step of Stacks 06H0, part (2).** Let `f : B ⟶ A` be a surjection in `𝒞_Λ` and let
`D` be a `Λ`-derivation of `B` into `k` over the augmentation with `D t = 1` for some
`t ∈ 𝔪_B` whose image in `A` lies in `𝔪_A²`. Then `f` is not an essential surjection: the
subobject `C = {b ∈ B | D b = 0}` is proper, because `t ∉ C`, and still surjects onto `A`,
because a lift `b ∈ 𝔪_B` of a given element of `𝔪_A` modulo `𝔪_A²` can be corrected to
`b - u t` with `u ∈ C`, which changes its image in `A` only by an element of `𝔪_A²`. -/
theorem not_isEssentialSurjection_of_derivation (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (htA : f.hom t ∈ maximalIdeal A ^ 2) : ¬ IsEssentialSurjection f := by
  intro hess
  have hqt : q t = 0 := (aug_eq_zero_iff q hq t).mpr ht
  have hgf : Function.Surjective (derivationKerHom q hq D hD ht hDt ≫ f).hom := by
    rw [surjective_hom_iff_exists_sub_mem_sq]
    intro a ha
    obtain ⟨b, hb, hba⟩ := (surjective_hom_iff_exists_sub_mem_sq f).mp hf a ha
    obtain ⟨u, hu⟩ := kernelAug_surjective_of_mem_maximalIdeal q hq D hD ht hDt (D b)
    have hx : b - (u : B) * t ∈ kernelSubalgebra q D hD := by
      rw [mem_kernelSubalgebra, map_sub, hD, hqt, hDt, show q (u : B) = D b from hu]
      ring
    refine ⟨⟨b - (u : B) * t, hx⟩, ?_, ?_⟩
    · exact (mem_maximalIdeal_derivationKerObj q hq D hD ht hDt).mpr
        (Submodule.sub_mem _ hb (Ideal.mul_mem_left _ _ ht))
    · have hmap : (derivationKerHom q hq D hD ht hDt ≫ f).hom ⟨b - (u : B) * t, hx⟩ - a =
          f.hom b - a - f.hom (u : B) * f.hom t := by
        change f.hom (b - (u : B) * t) - a = _
        rw [map_sub, map_mul]
        ring
      rw [hmap]
      exact Submodule.sub_mem _ hba (Ideal.mul_mem_left _ _ htA)
  obtain ⟨x, hx⟩ := hess.2 (derivationKerHom q hq D hD ht hDt) hgf t
  refine one_ne_zero (α := k) (hDt.symm.trans ?_)
  rw [← hx]
  exact map_derivationKerHom q hq D hD ht hDt x

end DerivationKernel

/-! ### Stacks 06H0, parts (1) and (2) -/

/-- **Stacks 06H0**, part (1)(a). A morphism `f : B ⟶ A` of `𝒞_Λ` is surjective — equivalently,
satisfies the conditions of [Stacks, Tag 06S3] — exactly when `Im(d_B) → Im(d_A)` is
surjective. -/
@[stacks 06H0 "part (1)(a), the image of the differential"]
theorem surjective_iff_imageDMap_surjective (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (imageDMap f) := by
  constructor
  · intro hf
    have hcot := (surjective_hom_iff_surjective_cotangentMap f).mp hf
    intro w
    obtain ⟨z, hz⟩ := w.2
    obtain ⟨y, rfl⟩ := hcot z
    refine ⟨⟨(residueExt B).cotangentComplex y, ⟨y, rfl⟩⟩, Subtype.ext ?_⟩
    rwa [imageDMap_coe, Algebra.Extension.CotangentSpace.map_cotangentComplex]
  · intro h
    rw [surjective_hom_iff_surjective_cotangentMap]
    intro x
    obtain ⟨v, hv⟩ := h ⟨(residueExt A).cotangentComplex x, ⟨x, rfl⟩⟩
    obtain ⟨y, hy⟩ := v.2
    have hdiff : (residueExt A).cotangentComplex
        (x - Algebra.Extension.Cotangent.map (residueExtHom f) y) = 0 := by
      rw [map_sub, ← Algebra.Extension.CotangentSpace.map_cotangentComplex, hy,
        ← imageDMap_coe, hv, sub_self]
    obtain ⟨z, hz⟩ := (exact_h1ToCotangent A _).mp hdiff
    refine ⟨y + h1ToCotangent B z, ?_⟩
    rw [map_add, cotangentMap_residueExtHom_h1ToCotangent, hz]
    abel

/-- **Stacks 06H0**, part (1)(b). A morphism `f : B ⟶ A` of `𝒞_Λ` is surjective — equivalently,
satisfies the conditions of [Stacks, Tag 06S3] — exactly when
`Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is surjective. -/
@[stacks 06H0 "part (1)(b), the cotangent space"]
theorem surjective_iff_cotangentSpaceMap_residueExtHom_surjective (f : B ⟶ A) :
    Function.Surjective f.hom ↔
      Function.Surjective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) :=
  (surjective_iff_imageDMap_surjective f).trans
    (imageDMap_surjective_iff_cotangentSpaceMap_surjective f)

/-- **Stacks 06H0**, part (2), equivalence of conditions (b) and (c). For a morphism of `𝒞_Λ`
the map `Im(d_B) → Im(d_A)` is an isomorphism exactly when
`Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is one. -/
@[stacks 06H0 "part (2), conditions (b) and (c)"]
theorem imageDMap_bijective_iff_cotangentSpaceMap_bijective (f : B ⟶ A) :
    Function.Bijective (imageDMap f) ↔
      Function.Bijective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) :=
  and_congr (imageDMap_injective_iff_cotangentSpaceMap_injective f)
    (imageDMap_surjective_iff_cotangentSpaceMap_surjective f)

/-- If a functorial map `φ f : M B → M A` detects surjectivity of morphisms of `𝒞_Λ` and is
bijective for `f`, then `f` is an essential surjection: for `g ≫ f` surjective, `φ (g ≫ f)` is
surjective, hence so is `φ g` by injectivity of `φ f`. -/
private theorem isEssentialSurjection_of_bijective_map
    {M : ArtinianLocalAlgCat.{u, v, w} Λ k → Type*}
    (φ : ∀ {X Y : ArtinianLocalAlgCat.{u, v, w} Λ k}, (X ⟶ Y) → M X → M Y)
    (hcomp : ∀ {X Y Z : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : X ⟶ Y) (f : Y ⟶ Z) (x : M X),
      φ (g ≫ f) x = φ f (φ g x))
    (hsurj : ∀ {X Y : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : X ⟶ Y),
      Function.Surjective f.hom ↔ Function.Surjective (φ f))
    (f : B ⟶ A) (h : Function.Bijective (φ f)) : IsEssentialSurjection f := by
  refine ⟨(hsurj f).mpr h.2, fun g hg => (hsurj g).mpr fun w => ?_⟩
  obtain ⟨x, hx⟩ := (hsurj (g ≫ f)).mp hg (φ f w)
  exact ⟨x, h.1 (by rwa [← hcomp])⟩

/-- Half of **Stacks 06H0**, part (2): condition (c) implies condition (a). If
`Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is an isomorphism then `f` is an essential surjection. Indeed
`f` is surjective by part (1), and if `g ≫ f` is surjective then
`Ω_{C/Λ} ⊗_C k → Ω_{A/Λ} ⊗_A k` is surjective, which by injectivity of the second factor forces
`Ω_{C/Λ} ⊗_C k → Ω_{B/Λ} ⊗_B k` to be surjective, so `g` is surjective by part (1) again. -/
theorem isEssentialSurjection_of_cotangentSpaceMap_bijective (f : B ⟶ A)
    (h : Function.Bijective (Algebra.Extension.CotangentSpace.map (residueExtHom f))) :
    IsEssentialSurjection f := by
  exact isEssentialSurjection_of_bijective_map
    (M := fun X => (residueExt X).CotangentSpace)
    (fun f => Algebra.Extension.CotangentSpace.map (residueExtHom f))
    cotangentSpaceMap_residueExtHom_comp
    surjective_iff_cotangentSpaceMap_residueExtHom_surjective f h

/-- **Stacks 06H0**, part (2): condition (a) implies condition (c). If `f : B ⟶ A` is an
essential surjection of `𝒞_Λ` then `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is an isomorphism.

It is surjective by part (1). If it were not injective, choose `0 ≠ v` in its kernel and a
`k`-linear functional `λ` on `Ω_{B/Λ} ⊗_B k` with `λ v = 1`; then `D b = λ(1 ⊗ d b)` is a
`Λ`-derivation of `B` into `k` over the augmentation, and `v = 1 ⊗ d t` for some `t ∈ 𝔪_B`
whose image in `A` lies in `𝔪_A²` by `exists_cotangentComplex_mk_eq`, so `D t = 1` and
`not_isEssentialSurjection_of_derivation` contradicts the assumption. -/
theorem cotangentSpaceMap_bijective_of_isEssentialSurjection (f : B ⟶ A)
    (h : IsEssentialSurjection f) :
    Function.Bijective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) := by
  refine ⟨?_, (surjective_iff_cotangentSpaceMap_residueExtHom_surjective f).mp h.1⟩
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra hvne
  obtain ⟨lam, hlam⟩ := Module.Projective.exists_dual_eq_one k hvne
  obtain ⟨t, htk, htA, htv⟩ := exists_cotangentComplex_mk_eq f hv
  have ht : t ∈ maximalIdeal B := (residueExt_ker B).le htk
  let mu : Ω[B⁄Λ] →ₗ[B] k := lam.restrictScalars B ∘ₗ TensorProduct.mk B k Ω[B⁄Λ] 1
  let Der : Derivation Λ B k := mu.compDer (KaehlerDifferential.D Λ B)
  have hDleib : ∀ a b : B, (Der : B →ₗ[Λ] k) (a * b) =
      IsScalarTower.toAlgHom Λ B k a * (Der : B →ₗ[Λ] k) b +
        IsScalarTower.toAlgHom Λ B k b * (Der : B →ₗ[Λ] k) a := by
    intro a b
    have hleib := Der.leibniz a b
    rwa [Algebra.smul_def, Algebra.smul_def] at hleib
  have hDt : (Der : B →ₗ[Λ] k) t = 1 := by
    have hval : (Der : B →ₗ[Λ] k) t =
        lam ((residueExt B).cotangentComplex (Algebra.Extension.Cotangent.mk ⟨t, htk⟩)) := rfl
    rwa [hval, htv]
  exact not_isEssentialSurjection_of_derivation (IsScalarTower.toAlgHom Λ B k)
    (fun a => (algebraMap_eq_residue B a).symm) (Der : B →ₗ[Λ] k) hDleib ht hDt f h.1 htA h

/-- **Stacks 06H0**, part (2), equivalence of conditions (a) and (c). A morphism of `𝒞_Λ` is an
essential surjection exactly when `Ω_{B/Λ} ⊗_B k → Ω_{A/Λ} ⊗_A k` is an isomorphism. -/
@[stacks 06H0 "part (2), conditions (a) and (c)"]
theorem isEssentialSurjection_iff_cotangentSpaceMap_bijective (f : B ⟶ A) :
    IsEssentialSurjection f ↔
      Function.Bijective (Algebra.Extension.CotangentSpace.map (residueExtHom f)) :=
  ⟨cotangentSpaceMap_bijective_of_isEssentialSurjection f,
    isEssentialSurjection_of_cotangentSpaceMap_bijective f⟩

/-- **Stacks 06H0**, part (2), equivalence of conditions (a) and (b). A morphism of `𝒞_Λ` is an
essential surjection exactly when `Im(d_B) → Im(d_A)` is an isomorphism. -/
@[stacks 06H0 "part (2), conditions (a) and (b)"]
theorem isEssentialSurjection_iff_imageDMap_bijective (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (imageDMap f) :=
  (isEssentialSurjection_iff_cotangentSpaceMap_bijective f).trans
    (imageDMap_bijective_iff_cotangentSpaceMap_bijective f).symm

/-! ### Stacks 06H0, part (3) -/

/-- The map `𝔪_B/(𝔪_Λ B + 𝔪_B²) → 𝔪_A/(𝔪_Λ A + 𝔪_A²)` induced by a morphism of `𝒞_Λ` sends the
class of `y ∈ 𝔪_B` to the class of `f y`. -/
theorem relativeCotangentSpaceMap_mk (f : B ⟶ A) (y : maximalIdeal B) :
    relativeCotangentSpaceMap f (Submodule.mkQ (relativeCotangentSubmodule B) y) =
      Submodule.mkQ (relativeCotangentSubmodule A) (maximalIdealMap f y) := rfl

/-- `𝔪/(𝔪_Λ · + 𝔪²)` is functorial on `𝒞_Λ`. -/
@[sga "7 VI 1.7" "partial"]
theorem relativeCotangentSpaceMap_comp {C : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : C ⟶ B) (f : B ⟶ A) (x : relativeCotangentSpaceOverBase C) :
    relativeCotangentSpaceMap (g ≫ f) x =
      relativeCotangentSpaceMap f (relativeCotangentSpaceMap g x) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (relativeCotangentSubmodule C) x
  rw [relativeCotangentSpaceMap_mk, relativeCotangentSpaceMap_mk, relativeCotangentSpaceMap_mk]
  exact congrArg _ (Subtype.ext rfl)

/-- The criterion of [Stacks, Tag 06S3] on the relative cotangent space: a morphism of `𝒞_Λ` is
surjective exactly when `𝔪_B/(𝔪_Λ B + 𝔪_B²) → 𝔪_A/(𝔪_Λ A + 𝔪_A²)` is surjective. -/
theorem surjective_hom_iff_surjective_relativeCotangentSpaceMap (f : B ⟶ A) :
    Function.Surjective f.hom ↔ Function.Surjective (relativeCotangentSpaceMap f) :=
  (surjective_iff_cotangentSpaceMap_surjective f).trans
    (cotangentSpaceMap_surjective_iff_relativeCotangentSpaceMap_surjective f)

/-- Half of **Stacks 06H0**, part (3), and the half that needs no separability: if
`𝔪_B/(𝔪_Λ B + 𝔪_B²) → 𝔪_A/(𝔪_Λ A + 𝔪_A²)` is an isomorphism then `f` is an essential
surjection. The argument is the one of
`isEssentialSurjection_of_cotangentSpaceMap_bijective`, run on the relative cotangent space,
which is functorial by `relativeCotangentSpaceMap_comp`. -/
theorem isEssentialSurjection_of_relativeCotangentSpaceMap_bijective (f : B ⟶ A)
    (h : Function.Bijective (relativeCotangentSpaceMap f)) : IsEssentialSurjection f := by
  exact isEssentialSurjection_of_bijective_map (M := relativeCotangentSpaceOverBase)
    (fun f => relativeCotangentSpaceMap f) relativeCotangentSpaceMap_comp
    surjective_hom_iff_surjective_relativeCotangentSpaceMap f h

/-- The differential `d_A : 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` kills the class of every element of
`𝔪_Λ A + 𝔪_A²`: it kills `𝔪_A²` because it is defined on `𝔪_A/𝔪_A²`, and it kills the structural
image of `𝔪_Λ` because `d` is a `Λ`-derivation, so that `d` of the image of `λ ∈ Λ` vanishes;
the ideal generated by those images is handled by `Ideal.map_le_iff_le_comap`, since the
elements of `𝔪_A` killed by `d_A` form an ideal of `A`. -/
theorem cotangentComplex_mk_eq_zero_of_mem_relative
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {y : A} (hy : y ∈ (residueExt A).ker)
    (h : y ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2) :
    (residueExt A).cotangentComplex (Algebra.Extension.Cotangent.mk ⟨y, hy⟩) = 0 := by
  have hker : RingHom.ker (algebraMap A k) = maximalIdeal A := residueExt_ker A
  have hker2 : RingHom.ker (algebraMap A k) ^ 2 = maximalIdeal A ^ 2 :=
    congrArg (fun I => I ^ 2) hker
  have hle : (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2 ≤
      Submodule.map (RingHom.ker (algebraMap A k)).subtype
        (LinearMap.ker (KaehlerDifferential.kerCotangentToTensor Λ A k ∘ₗ
          (RingHom.ker (algebraMap A k)).toCotangent)) := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro lam hlam
      have hmem : algebraMap Λ A lam ∈ RingHom.ker (algebraMap A k) := by
        rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply Λ A k]
        exact hlam
      refine ⟨⟨algebraMap Λ A lam, hmem⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      rw [LinearMap.comp_apply, KaehlerDifferential.kerCotangentToTensor_toCotangent,
        Derivation.map_algebraMap, TensorProduct.tmul_zero]
    · intro x hx
      have hxI : x ∈ RingHom.ker (algebraMap A k) :=
        hker.ge ((Ideal.pow_le_self two_ne_zero) hx)
      refine ⟨⟨x, hxI⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      rw [LinearMap.comp_apply, show (RingHom.ker (algebraMap A k)).toCotangent ⟨x, hxI⟩ = 0 from
        (Ideal.toCotangent_eq_zero _ _).mpr (hker2.ge hx), map_zero]
  obtain ⟨w, hwW, hwy⟩ := hle h
  have hzero : KaehlerDifferential.kerCotangentToTensor Λ A k
      ((RingHom.ker (algebraMap A k)).toCotangent w) = 0 := LinearMap.mem_ker.mp hwW
  rw [show w = ⟨y, hy⟩ from Subtype.ext hwy] at hzero
  rwa [cotangentComplex_residueExt_apply, Algebra.Extension.Cotangent.val_mk]

/-- The composite `𝔪_Λ/𝔪_Λ² → H₁(L_{k/Λ}) → 𝔪_A/𝔪_A²` is the map induced by the structural map
`𝔪_Λ → 𝔪_A`. This is `Deformation.conormalToH1Cotangent_comp` read through the identification
`𝔪_A/𝔪_A² = H₁(L_{k/A})` of [Stacks, Tag 06S9]. -/
theorem h1CotangentToCotangent_conormalToH1Cotangent
    {S : Type*} [Field S] [Algebra Λ S] [Algebra S k] [IsScalarTower Λ S k]
    (hS : Function.Surjective (algebraMap Λ S)) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (x : (RingHom.ker (algebraMap Λ S)).Cotangent) :
    h1CotangentToCotangent Λ (algebraMap_residue_surjective A)
        (conormalToH1Cotangent (Λ := Λ) (S := S) (k := k) hS x) =
      Ideal.mapCotangent (RingHom.ker (algebraMap Λ S))
        (RingHom.ker (algebraMap A k)) (Algebra.ofId Λ A)
        (ker_algebraMap_le_comap_ker (Λ := Λ) (S := S) (k := k) (A := A)) x := by
  have hcomp := conormalToH1Cotangent_comp (Λ := Λ) (S := S) (k := k) (A := A) hS
    (algebraMap_residue_surjective A) x
  rw [h1CotangentToCotangent, LinearMap.comp_apply, LinearMap.coe_restrictScalars, hcomp]
  exact (cotangentEquivH1Cotangent (algebraMap_residue_surjective A)).symm_apply_apply _

/-- **Stacks 06S9** in use: when `k` is separable over the image field `S = k'`, the kernel of
`d_A : 𝔪_A/𝔪_A² → Ω_{A/Λ} ⊗_A k` is no bigger than the image of `𝔪_Λ A + 𝔪_A²`.

By the four-term sequence of [Stacks, Tag 06S7] that kernel is the image of `H₁(L_{k/Λ})`, and
by `Deformation.conormalToH1Cotangent_baseChange_bijective` every class of `H₁(L_{k/Λ})` is a
`k`-linear combination of classes coming from `𝔪_Λ/𝔪_Λ²`. Since `A → k` is surjective those
`k`-coefficients may be taken in `A`, and `Deformation.conormalToH1Cotangent_comp` identifies
the image of a class of `𝔪_Λ/𝔪_Λ²` in `𝔪_A/𝔪_A²` with the class of its structural image, which
lies in `𝔪_Λ A`. -/
theorem mem_relative_of_cotangentComplex_mk_eq_zero
    {S : Type*} [Field S] [Algebra Λ S] [Algebra S k] [IsScalarTower Λ S k]
    (hS : Function.Surjective (algebraMap Λ S)) [Algebra.IsSeparable S k]
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {y : A} (hy : y ∈ (residueExt A).ker)
    (h : (residueExt A).cotangentComplex (Algebra.Extension.Cotangent.mk ⟨y, hy⟩) = 0) :
    y ∈ (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A) + maximalIdeal A ^ 2 := by
  have hker2 : RingHom.ker (algebraMap A k) ^ 2 = maximalIdeal A ^ 2 :=
    congrArg (fun I => I ^ 2) (residueExt_ker A)
  have hSk : RingHom.ker (algebraMap Λ S) ≤ RingHom.ker (algebraMap Λ k) := by
    intro lam hlam
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply Λ S k,
      show algebraMap Λ S lam = 0 from hlam, map_zero]
  obtain ⟨z, hz⟩ := (exact_h1ToCotangent A _).mp h
  have hgen : ∀ x : (RingHom.ker (algebraMap Λ S)).Cotangent,
      h1CotangentToCotangent Λ (algebraMap_residue_surjective A)
          (conormalToH1Cotangent (Λ := Λ) (S := S) (k := k) hS x) ∈
        Submodule.map (RingHom.ker (algebraMap A k)).toCotangent
          (Submodule.comap (RingHom.ker (algebraMap A k)).subtype
            ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A))) := by
    intro x
    obtain ⟨⟨lam, hlam⟩, rfl⟩ := (RingHom.ker (algebraMap Λ S)).toCotangent_surjective x
    have hrfl : Ideal.mapCotangent (RingHom.ker (algebraMap Λ S))
        (RingHom.ker (algebraMap A k)) (Algebra.ofId Λ A)
        (ker_algebraMap_le_comap_ker (Λ := Λ) (S := S) (k := k) (A := A))
        ((RingHom.ker (algebraMap Λ S)).toCotangent ⟨lam, hlam⟩) =
      (RingHom.ker (algebraMap A k)).toCotangent
        ⟨algebraMap Λ A lam,
          ker_algebraMap_le_comap_ker (Λ := Λ) (S := S) (k := k) (A := A) hlam⟩ := rfl
    rw [h1CotangentToCotangent_conormalToH1Cotangent hS A, hrfl]
    exact Submodule.mem_map_of_mem (Ideal.mem_map_of_mem _ (hSk hlam))
  have hall : ∀ z : Algebra.H1Cotangent Λ k,
      h1CotangentToCotangent Λ (algebraMap_residue_surjective A) z ∈
        Submodule.map (RingHom.ker (algebraMap A k)).toCotangent
          (Submodule.comap (RingHom.ker (algebraMap A k)).subtype
            ((RingHom.ker (algebraMap Λ k)).map (algebraMap Λ A))) := by
    intro z
    obtain ⟨ζ, rfl⟩ :=
      (conormalToH1Cotangent_baseChange_bijective (Λ := Λ) (S := S) (k := k) hS).2 z
    induction ζ using TensorProduct.inductionOn with
    | tmul c x =>
      obtain ⟨b, hb⟩ := algebraMap_residue_surjective A c
      rw [LinearMap.liftBaseChange_tmul, ← hb, IsScalarTower.algebraMap_smul k b,
        LinearMap.map_smul]
      exact Submodule.smul_mem _ b (hgen x)
    | add ζ₁ ζ₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  have hval : h1CotangentToCotangent Λ (algebraMap_residue_surjective A) z =
      (RingHom.ker (algebraMap A k)).toCotangent ⟨y, hy⟩ :=
    congrArg Algebra.Extension.Cotangent.val hz
  obtain ⟨wv, hwv, hwveq⟩ := hval ▸ hall z
  have hsub : ((wv : A) - y) ∈ maximalIdeal A ^ 2 :=
    hker2.le (((RingHom.ker (algebraMap A k)).toCotangent_eq).mp hwveq)
  refine Submodule.mem_sup.mpr ⟨(wv : A), hwv, y - (wv : A), ?_, by ring⟩
  rw [← neg_sub]
  exact Submodule.neg_mem _ hsub

/-- **Stacks 06H0**, part (3). If `k` is separable over the image field `k'` — presented as a
field `S` with `Λ → S` surjective and `S → k` separable — then a morphism `f : B ⟶ A` of `𝒞_Λ`
is an essential surjection exactly when
`𝔪_B/(𝔪_Λ B + 𝔪_B²) → 𝔪_A/(𝔪_Λ A + 𝔪_A²)` is an isomorphism.

In that case `Im(d_A) = 𝔪_A/(𝔪_Λ A + 𝔪_A²)` for every object `A`, by
`cotangentComplex_mk_eq_zero_of_mem_relative` and
`mem_relative_of_cotangentComplex_mk_eq_zero`, and the statement follows from part (2). Only
the forward implication uses separability: the converse is
`isEssentialSurjection_of_relativeCotangentSpaceMap_bijective`. -/
@[stacks 06H0 "part (3), separable case"]
theorem isEssentialSurjection_iff_relativeCotangentSpaceMap_bijective
    {S : Type*} [Field S] [Algebra Λ S] [Algebra S k] [IsScalarTower Λ S k]
    (hS : Function.Surjective (algebraMap Λ S)) [Algebra.IsSeparable S k] (f : B ⟶ A) :
    IsEssentialSurjection f ↔ Function.Bijective (relativeCotangentSpaceMap f) := by
  refine ⟨fun h => ⟨?_, (surjective_hom_iff_surjective_relativeCotangentSpaceMap f).mp h.1⟩,
    isEssentialSurjection_of_relativeCotangentSpaceMap_bijective f⟩
  have hinj := (cotangentSpaceMap_bijective_of_isEssentialSurjection f h).1
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (relativeCotangentSubmodule B) ξ
  rw [relativeCotangentSpaceMap_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hξ
  have hyB : (y : B) ∈ (residueExt B).ker := (residueExt_ker B).ge y.2
  have hdB : (residueExt B).cotangentComplex
      (Algebra.Extension.Cotangent.mk ⟨(y : B), hyB⟩) = 0 := by
    refine (injective_iff_map_eq_zero
      (Algebra.Extension.CotangentSpace.map (residueExtHom f))).mp hinj _ ?_
    rw [Algebra.Extension.CotangentSpace.map_cotangentComplex,
      cotangentMap_residueExtHom_mk f (y : B) hyB]
    exact cotangentComplex_mk_eq_zero_of_mem_relative A _ hξ
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact mem_relative_of_cotangentComplex_mk_eq_zero hS B hyB hdB

end ArtinianLocalAlgCat

end Deformation

end
