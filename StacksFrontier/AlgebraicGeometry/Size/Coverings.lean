module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Sets.CompactOpenCovered
public import StacksFrontier.AlgebraicGeometry.Size.Basic
import StacksFrontier.AlgebraicGeometry.Size.FiniteType
import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# Coverings of bounded size: fpqc and fppf refinements

## Scheme size and fpqc coverings that factor through a morphism (Stacks 0AHK)

Let `f : X ⟶ Y` be a morphism of schemes. If `Y` admits an fpqc covering
`{g j : Y' j ⟶ Y}` in which every `g j` factors through `f`, then `Y.size ≤ X.size`.
Here `AlgebraicGeometry.Scheme.size` is the size of a scheme in the sense of Stacks
*Sets*, Section 3.9 — the maximum of `ℵ₀`, the number of affine opens, and the supremum of
`#Γ(S, U)` over affine opens `U`. It is reused from `StacksFrontier.AlgebraicGeometry.Size.Basic`
and is never redefined here.

`IsFpqcCovering` reproduces the definition of an fpqc covering from Stacks 03L7: each
`g j` is flat, and every affine open `U` of the target is a *finite* union
`U = ⋃ i, g (a i) '' V i` of images of affine opens `V i ⊆ Y' (a i)`, with each of those
images contained in `U`. Mathlib also knows the fpqc topology, as the precoverage
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, but it is defined differently — by flatness
together with a quasi-compact surjective refinement rather than by refinement into affine
opens — so identifying the two notions is a compatibility statement in its own right and
is deliberately not treated here. This file works with the affine-refinement form,
because that is the form the proof consumes.

The proof splits along the two cardinals that `Scheme.size` maximizes.

* Affine opens. For an affine open `U ⊆ Y` the covering condition, together with the
  factorizations `h j ≫ f = g j`, exhibits `U` as the image under `f` of the quasi-compact
  set `⋃ i, h (a i) '' V i ⊆ f ⁻¹ᵁ U`; covering that set by finitely many affine opens of
  `X` produces a finite set of affine opens of `X` whose image under `f` is exactly `U`.
  Distinct `U` therefore receive distinct finite sets, giving
  `#Y.affineOpens ≤ #(Finset X.affineOpens) ≤ max ℵ₀ #X.affineOpens`.
* Sections. On such a finite cover `W` of `f ⁻¹ᵁ U` the combined restriction
  `Γ(Y, U) → ∏ i, Γ(X, W i)` is injective. This is the descent step: `g (a i)` is flat and
  its stalk maps are local homomorphisms of local rings, hence faithfully flat, hence
  injective; since `g (a i) = h (a i) ≫ f`, the stalk map of `f` at each point
  `h (a i) v` is injective as well, and a section over `U` is determined by its germs at
  those points. A finite product of cardinals bounded by `X.size` is again bounded by
  `X.size`.

## Refining an fppf covering to one of bounded size (Stacks 0AHL)

Every fppf covering `𝒞` of a scheme `X`, with index type in an arbitrary universe, is
refined by an fppf covering `𝒲` indexed in the universe of `X` and small enough that the
coproduct of its members satisfies `Scheme.size (∐ 𝒲.X) ≤ Scheme.size X`. Here
`AlgebraicGeometry.Scheme.size` is the size of a scheme in the sense of Stacks *Sets*,
Section 3.9, reused from `StacksFrontier.AlgebraicGeometry.Size.Basic`; the bound on the size of a
coproduct is `StacksFrontier.AlgebraicGeometry.Size.OpenCover`.

The refinement is built affine open by affine open. A flat morphism locally of finite
presentation is open (`AlgebraicGeometry.UniversallyOpen.of_flat`), so the images of the
affine opens of the members of `𝒞` form an open cover of `X`; an affine open `U ⊆ X` is
quasi-compact, so finitely many of them already cover `U`. Indexing those finite families
by the affine opens of `X` gives an index type `Σ U : X.affineOpens, Fin (n U)`, which
lies in the universe of `X` and has at most `Scheme.size X` elements. Each member is an
affine open `V` of some `𝒞.X i`; the composite `V ⟶ 𝒞.X i ⟶ X` is locally of finite type
and `V` is quasi-compact, so `Scheme.size V ≤ Scheme.size X` by Stacks 04T7. The bound for
the coproduct is then Stacks 000Q.
-/

@[expose] public section

open CategoryTheory Cardinal TopologicalSpace

namespace Cardinal

/-- The number of finite subsets of `α` is at most `max ℵ₀ #α`. -/
private lemma mk_finset_le_max_aleph0 (α : Type*) : #(Finset α) ≤ max ℵ₀ #α := by
  rcases finite_or_infinite α with hfin | hinf
  · have : Finite α := hfin
    exact le_max_of_le_left (lt_aleph0_of_finite (Finset α)).le
  · exact (mk_finset_of_infinite α).le.trans (le_max_right _ _)

/-- A product of finitely many cardinals, each at most an infinite cardinal `κ`, is at
most `κ`. -/
private lemma prod_fin_le {n : ℕ} {κ : Cardinal} (hκ : ℵ₀ ≤ κ) (f : Fin n → Cardinal)
    (hf : ∀ i, f i ≤ κ) : ∏ i : Fin n, f i ≤ κ :=
  calc ∏ i : Fin n, f i
      ≤ ∏ _i : Fin n, κ := Finset.prod_le_prod₀ (fun _ _ => bot_le) fun i _ => hf i
    _ = κ ^ n := by simp
    _ ≤ κ := power_nat_le hκ

end Cardinal

namespace AlgebraicGeometry

/-- An **fpqc covering** of a scheme `T`: a family of morphisms `g j : Y j ⟶ T` such that
every `g j` is flat and every affine open of `T` is a finite union of images of affine
opens of the `Y j`, each such image contained in the given affine open.

This is Stacks 03L7 (Topologies, Definition 34.9.1). Mathlib's fpqc topology,
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, uses an equivalent but differently phrased
condition; the two are not identified here. -/
structure IsFpqcCovering {T : Scheme} {J : Type*} (Y : J → Scheme)
    (g : ∀ j, Y j ⟶ T) : Prop where
  /-- Each morphism in the family is flat. -/
  flat : ∀ j, Flat (g j)
  /-- Each affine open `U` of `T` is a finite union `U = ⋃ i, g (a i) '' V i` of images of
  affine opens `V i` of members of the family, all of those images lying inside `U`. -/
  covers : ∀ U : T.Opens, IsAffineOpen U →
    ∃ (n : ℕ) (a : Fin n → J) (V : ∀ i : Fin n, (Y (a i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      (∀ i, ((g (a i)) '' (V i : Set (Y (a i))) : Set T) ⊆ (U : Set T)) ∧
      ((U : Set T) =
        ⋃ i : Fin n, ((g (a i)) '' (V i : Set (Y (a i))) : Set T))

/-- A compact subset of an open `W` of a scheme is covered by finitely many affine opens
that are themselves contained in `W`. -/
lemma exists_affineOpens_cover_of_isCompact (X : Scheme) (K : Set X)
    (hK : IsCompact K) (W : X.Opens) (hKW : K ⊆ (W : Set X)) :
    ∃ (m : ℕ) (A : Fin m → X.affineOpens),
      (∀ j, (A j).1 ≤ W) ∧ K ⊆ ⋃ j : Fin m, ((A j).1 : Set X) := by
  have hcov : K ⊆ ⋃ A ∈ {A : X.affineOpens | A.1 ≤ W}, (A.1 : Set X) := fun x hx => by
    obtain ⟨s, ⟨A, hAaff, rfl⟩, hxs, hsW⟩ :=
      (Scheme.isBasis_affineOpens X).mem_nhds_iff.mp (W.isOpen.mem_nhds (hKW hx))
    exact Set.mem_biUnion (x := (⟨A, hAaff⟩ : X.affineOpens)) hsW hxs
  obtain ⟨B, hBW, hBfin, hBcov⟩ := hK.elim_finite_subcover_image (fun A _ => A.1.isOpen) hcov
  set t := hBfin.toFinset
  refine ⟨t.card, fun i => t.equivFin.symm i,
    fun j => hBW (hBfin.mem_toFinset.mp (t.equivFin.symm j).2), fun x hx => ?_⟩
  obtain ⟨A, hAB, hxA⟩ := Set.mem_iUnion₂.mp (hBcov hx)
  exact Set.mem_iUnion.mpr ⟨t.equivFin ⟨A, hBfin.mem_toFinset.mpr hAB⟩, by simpa using hxA⟩

/-- If `h ≫ f = g`, then `f` carries the image of a point under `h` to its image under
`g`. -/
private lemma base_apply_of_comp_eq {X Y Z : Scheme} {f : X ⟶ Y} {h : Z ⟶ X} {g : Z ⟶ Y}
    (hh : h ≫ f = g) (v : Z) : f.base (h.base v) = g.base v := by rw [← hh]; rfl

/-- If every `g (a i)` maps `V i` into an open `U` of `Y` and `h j ≫ f = g j`, then the
images of the `V i` under the `h (a i)` all lie in `f ⁻¹ᵁ U`. -/
private lemma iUnion_image_subset_preimage {X Y : Scheme} (f : X ⟶ Y) {J : Type*}
    {Y' : J → Scheme} {g : ∀ j, Y' j ⟶ Y} {h : ∀ j, Y' j ⟶ X} (hh : ∀ j, h j ≫ f = g j)
    {n : ℕ} {a : Fin n → J} {V : ∀ i : Fin n, (Y' (a i)).Opens} {U : Y.Opens}
    (hVsub : ∀ i, ((g (a i)) '' (V i : Set (Y' (a i))) : Set Y) ⊆ (U : Set Y)) :
    (⋃ i : Fin n, ((h (a i)) '' (V i : Set (Y' (a i))) : Set X)) ⊆ (f ⁻¹ᵁ U : Set X) :=
  Set.iUnion_subset fun i x ⟨v, hv, hvx⟩ => by
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage]
    have hbase : f.base x = (g (a i)).base v := by
      rw [← hvx]; exact base_apply_of_comp_eq (hh (a i)) v
    rw [hbase]
    exact hVsub i ⟨v, hv, rfl⟩

/-- The stalk map of a flat morphism of schemes is injective at every point: it is a flat
local homomorphism of local rings, hence faithfully flat. -/
private lemma stalkMap_injective_of_flat {Y Z : Scheme} (g : Z ⟶ Y) (hg : Flat g) (v : Z) :
    Function.Injective (ConcreteCategory.hom (g.stalkMap v)) := by
  have : Flat g := hg
  have hflat : (g.stalkMap v).hom.Flat := Flat.stalkMap g v
  let := (g.stalkMap v).hom.toAlgebra
  have : IsLocalHom (algebraMap (↑(Y.presheaf.stalk (g.base v))) (↑(Z.presheaf.stalk v))) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.Flat (↑(Y.presheaf.stalk (g.base v))) (↑(Z.presheaf.stalk v)) := hflat
  exact RingHom.FaithfullyFlat.injective Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Under the hypotheses of Stacks 0AHK, an affine open `U ⊆ Y` has a finite cover of
`f ⁻¹ᵁ U` by affine opens of `X` such that every point of `U` is the image of a point of one
of them at which the stalk map of `f` is injective. -/
private lemma exists_affineOpens_cover_fpqc {X Y : Scheme} (f : X ⟶ Y)
    {J : Type*} (Y' : J → Scheme) (g : ∀ j, Y' j ⟶ Y)
    (hcov : IsFpqcCovering Y' g)
    (h : ∀ j, Y' j ⟶ X) (hh : ∀ j, h j ≫ f = g j) (U : Y.affineOpens) :
    ∃ (m : ℕ) (A : Fin m → X.affineOpens), (∀ j, (A j).1 ≤ f ⁻¹ᵁ U.1) ∧
      ∀ y ∈ U.1, ∃ j, ∃ x ∈ (A j).1, f.base x = y ∧
        Function.Injective (ConcreteCategory.hom (f.stalkMap x)) := by
  obtain ⟨n, a, V, hVaff, hVsub, hVcover⟩ := hcov.covers U.1 U.2
  have hcompact : IsCompact (⋃ i : Fin n, (h (a i)) '' (V i : Set (Y' (a i)))) :=
    isCompact_iUnion fun i => (hVaff i).isCompact.image (h (a i)).continuous
  obtain ⟨m, A, hAle, hAcov⟩ := exists_affineOpens_cover_of_isCompact X _ hcompact
    (f ⁻¹ᵁ U.1) (iUnion_image_subset_preimage f hh hVsub)
  refine ⟨m, A, hAle, fun y hy => ?_⟩
  have hy_union : y ∈ ⋃ i : Fin n, ((g (a i)) '' (V i : Set (Y' (a i))) : Set Y) := by
    rw [← hVcover]; exact hy
  obtain ⟨i, v, hv, hvy⟩ := Set.mem_iUnion.mp hy_union
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (hAcov (Set.mem_iUnion.mpr ⟨i, v, hv, rfl⟩))
  refine ⟨j, (h (a i)).base v, hxj, (base_apply_of_comp_eq (hh (a i)) v).trans hvy, ?_⟩
  have hcomp_inj : Function.Injective (ConcreteCategory.hom ((h (a i) ≫ f).stalkMap v)) := by
    rw [hh (a i)]; exact stalkMap_injective_of_flat (g (a i)) (hcov.flat (a i)) v
  rw [show (h (a i) ≫ f).stalkMap v = f.stalkMap ((h (a i)).base v) ≫ (h (a i)).stalkMap v from
    Scheme.Hom.stalkMap_comp (h (a i)) f v] at hcomp_inj
  exact (show Function.Injective (ConcreteCategory.hom ((h (a i)).stalkMap v) ∘
    ConcreteCategory.hom (f.stalkMap ((h (a i)).base v))) from hcomp_inj).of_comp

open Classical in
/-- Under the hypotheses of Stacks 0AHK, the affine opens of `Y` inject into the finite
subsets of the affine opens of `X`.

An affine open `U ⊆ Y` is sent to a finite set of affine opens of `X`, contained in
`f ⁻¹ᵁ U` and covering the quasi-compact set `⋃ i, h (a i) '' V i`, whose image under `f`
is therefore exactly `U`; so `U` is recoverable from its finite set. -/
private lemma mk_affineOpens_le_mk_finset_affineOpens {X Y : Scheme} (f : X ⟶ Y)
    {J : Type*} (Y' : J → Scheme) (g : ∀ j, Y' j ⟶ Y)
    (hcov : IsFpqcCovering Y' g)
    (h : ∀ j, Y' j ⟶ X) (hh : ∀ j, h j ≫ f = g j) :
    #Y.affineOpens ≤ #(Finset X.affineOpens) := by
  have aux : ∀ W : Y.affineOpens, ∃ S : Finset X.affineOpens,
      (∀ A ∈ S, (A.1 : Set X) ⊆ f.base ⁻¹' (W.1 : Set Y)) ∧
      (W.1 : Set Y) ⊆ f.base '' (⋃ A ∈ S, (A.1 : Set X)) := by
    intro W
    obtain ⟨m, A, hAle, hA⟩ := exists_affineOpens_cover_fpqc f Y' g hcov h hh W
    refine ⟨Finset.image A Finset.univ, ?_, fun y hy => ?_⟩
    · intro B hB
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hB
      exact hAle j
    · obtain ⟨j, x, hx, rfl, -⟩ := hA y hy
      exact ⟨x, Set.mem_biUnion (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩) hx, rfl⟩
  -- The chosen finite set determines its affine open, because `f` maps it onto it.
  have key : ∀ W : Y.affineOpens,
      f.base '' (⋃ A ∈ (aux W).choose, (A.1 : Set X)) = (W.1 : Set Y) := fun W => by
    obtain ⟨hmem, hsup⟩ := (aux W).choose_spec
    refine Set.Subset.antisymm (Set.image_subset_iff.mpr fun x hx => ?_) hsup
    obtain ⟨A, hA, hxA⟩ := Set.mem_iUnion₂.mp hx
    exact hmem A hA hxA
  apply mk_le_of_injective (f := fun W => (aux W).choose)
  intro U V hUV
  refine Subtype.ext (Opens.ext ?_)
  rw [← key U, ← key V, show (aux U).choose = (aux V).choose from hUV]

/-- Under the hypotheses of Stacks 0AHK, the sections over an affine open `U ⊆ Y` inject
into a finite product of section rings of `X` over affine opens contained in `f ⁻¹ᵁ U`.

The affine opens are obtained by covering the quasi-compact set `⋃ i, h (a i) '' V i`.
Injectivity is the fpqc descent step: the stalk maps of the flat morphisms `g (a i)` are
faithfully flat, hence injective, and they factor through the stalk maps of `f`. -/
private lemma exists_affineOpens_mk_sections_le_prod {X Y : Scheme} (f : X ⟶ Y)
    {J : Type*} (Y' : J → Scheme) (g : ∀ j, Y' j ⟶ Y)
    (hcov : IsFpqcCovering Y' g)
    (h : ∀ j, Y' j ⟶ X) (hh : ∀ j, h j ≫ f = g j)
    (U : Y.affineOpens) :
    ∃ (n : ℕ) (W : Fin n → X.affineOpens),
      #Γ(Y, U.1) ≤ ∏ i : Fin n, #Γ(X, (W i).1) := by
  obtain ⟨M, W, hWle, hW⟩ := exists_affineOpens_cover_fpqc f Y' g hcov h hh U
  refine ⟨M, W, ?_⟩
  suffices hinj : Function.Injective
      (fun s : Γ(Y, U.1) => fun j : Fin M => (f.appLE U.1 (W j).1 (hWle j)) s) by
    calc #Γ(Y, U.1)
        ≤ #((j : Fin M) → Γ(X, (W j).1)) := mk_le_of_injective hinj
      _ = ∏ j : Fin M, #Γ(X, (W j).1) := by rw [mk_pi, prod_eq_of_fintype]; simp
  intro s t hst
  have hst' : ∀ j, (ConcreteCategory.hom (f.appLE U.1 (W j).1 (hWle j))) s =
      (ConcreteCategory.hom (f.appLE U.1 (W j).1 (hWle j))) t := fun j => congr_fun hst j
  apply TopCat.Presheaf.section_ext Y.sheaf U.1
  intro y hy
  obtain ⟨j, x, hx_mem, rfl, hf_stalk_inj⟩ := hW y hy
  -- The germ at `x` of the restriction of a section along `f` is its germ pushed forward.
  have key : ∀ r : Γ(Y, U.1), (ConcreteCategory.hom (X.presheaf.germ (W j).1 x hx_mem))
        ((ConcreteCategory.hom (f.appLE U.1 (W j).1 (hWle j))) r) =
      (ConcreteCategory.hom (f.stalkMap x))
        ((ConcreteCategory.hom (Y.presheaf.germ U.1 (f.base x) hy)) r) := fun r => by
    unfold Scheme.Hom.appLE
    simp only [CommRingCat.comp_apply]
    rw [TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply]
  apply hf_stalk_inj
  change (ConcreteCategory.hom (f.stalkMap x))
      ((ConcreteCategory.hom (Y.presheaf.germ U.1 (f.base x) hy)) s) =
    (ConcreteCategory.hom (f.stalkMap x))
      ((ConcreteCategory.hom (Y.presheaf.germ U.1 (f.base x) hy)) t)
  rw [← key s, ← key t, hst' j]

/-- Under the hypotheses of Stacks 0AHK, the supremum of `#Γ(Y, U)` over affine opens `U`
of `Y` is bounded by `X.size`: each such cardinal embeds into a finite product of
`#Γ(X, W i)`, and a finite product of cardinals `≤ X.size` is `≤ X.size`. -/
private lemma iSup_mk_sections_le_size {X Y : Scheme} (f : X ⟶ Y)
    {J : Type*} (Y' : J → Scheme) (g : ∀ j, Y' j ⟶ Y)
    (hcov : IsFpqcCovering Y' g)
    (h : ∀ j, Y' j ⟶ X) (hh : ∀ j, h j ≫ f = g j) :
    (⨆ U : Y.affineOpens, #Γ(Y, U.1)) ≤ X.size :=
  ciSup_le' fun U => by
    obtain ⟨n, W, hle⟩ := exists_affineOpens_mk_sections_le_prod f Y' g hcov h hh U
    exact hle.trans (prod_fin_le X.aleph0_le_size _ fun i => X.mk_sections_le_size (W i))

/-- **Stacks 0AHK.** Let `f : X ⟶ Y` be a morphism of schemes. If there is an fpqc
covering `{g j : Y' j ⟶ Y}` of `Y` such that every `g j` factors through `f`, then
`Y.size ≤ X.size`. -/
@[stacks 0AHK]
theorem Scheme.size_le_of_fpqc_factorsThrough {X Y : Scheme} (f : X ⟶ Y)
    {J : Type*} (Y' : J → Scheme) (g : ∀ j, Y' j ⟶ Y)
    (hcov : IsFpqcCovering Y' g)
    (hfac : ∀ j, ∃ h : Y' j ⟶ X, h ≫ f = g j) :
    Scheme.size Y ≤ Scheme.size X := by
  choose h hh using hfac
  refine max_le X.aleph0_le_size (max_le ?_ (iSup_mk_sections_le_size f Y' g hcov h hh))
  calc #Y.affineOpens
      ≤ #(Finset X.affineOpens) := mk_affineOpens_le_mk_finset_affineOpens f Y' g hcov h hh
    _ ≤ max ℵ₀ #X.affineOpens := mk_finset_le_max_aleph0 _
    _ ≤ X.size := max_le X.aleph0_le_size X.mk_affineOpens_le_size

end AlgebraicGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace

universe w v u

/-- An **fppf covering** of a scheme `T`: a family of morphisms `{f i : X i ⟶ T}` such that
each `f i` is flat and locally of finite presentation, and the family is jointly surjective
on the underlying points of `T`. This is Stacks 021M. -/
structure FppfCovering (T : Scheme.{u}) where
  /-- The index type of the covering. -/
  ι : Type w
  /-- The schemes in the covering. -/
  X : ι → Scheme.{u}
  /-- The structure morphisms to `T`. -/
  f : ∀ i, X i ⟶ T
  /-- Each structure morphism is flat. -/
  flat : ∀ i, Flat (f i)
  /-- Each structure morphism is locally of finite presentation. -/
  lfp : ∀ i, LocallyOfFinitePresentation (f i)
  /-- The family is jointly surjective on the underlying points of `T`. -/
  jointly_surjective : ∀ t : T, ∃ i, ∃ x : X i, (f i).base x = t

/-- Refinement of fppf coverings of `T`: the covering `𝒲` refines `𝒞` when every
member of `𝒲` factors through some member of `𝒞` compatibly with the structure
morphisms to `T`. -/
def FppfCovering.IsRefinement {T : Scheme.{u}}
    (𝒲 : FppfCovering.{w} T) (𝒞 : FppfCovering.{v} T) : Prop :=
  ∀ j : 𝒲.ι, ∃ (i : 𝒞.ι) (g : 𝒲.X j ⟶ 𝒞.X i), g ≫ 𝒞.f i = 𝒲.f j

/-- A sigma type over `α` whose fibres are finite is bounded by any infinite cardinal
bounding `#α`: the sum of at most `#α` copies of a finite cardinal is at most
`#α * ℵ₀`. -/
private lemma Cardinal.mk_sigma_fin_le {α : Type u} (n : α → ℕ) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) (hα : #α ≤ κ) :
    #(Σ a : α, Fin (n a)) ≤ κ := by
  rw [Cardinal.mk_sigma]
  refine (sum_le_sum _ (fun _ => (ℵ₀ : Cardinal.{0})) fun _ => mk_lt_aleph0.le).trans ?_
  rw [sum_const, lift_uzero, lift_aleph0]
  exact (mul_le_mul' hα hκ).trans_eq (Cardinal.mul_eq_self hκ)

namespace FppfCovering

variable {T : Scheme.{u}} (𝒞 : FppfCovering.{v} T)

/-- Every structure morphism of an fppf covering is an open map: it is flat and locally of
finite presentation, hence universally open (Stacks 01UA). -/
lemma isOpenMap (i : 𝒞.ι) : IsOpenMap (𝒞.f i) := by
  have := 𝒞.flat i
  have := 𝒞.lfp i
  exact (𝒞.f i).isOpenMap

/-- Each affine open `U` of `T` is covered by the images of *finitely many* affine opens
of members of `𝒞`.

Indeed the structure morphisms of `𝒞` are open and jointly surjective, so the images of
the affine opens of the members form an open cover of `T`, and `U` is quasi-compact. -/
lemma exists_finite_affineOpens_cover (U : T.affineOpens) :
    ∃ (n : ℕ) (a : Fin n → 𝒞.ι) (V : ∀ k, (𝒞.X (a k)).Opens),
      (∀ k, IsAffineOpen (V k)) ∧
      ⋃ k, (𝒞.f (a k)) '' (V k : Set (𝒞.X (a k))) = (U.1 : Set T) := by
  have hcov : IsCompactOpenCovered (𝒞.f ·) (U.1 : Set T) :=
    .of_isOpenMap (fun i => (𝒞.f i).continuous) 𝒞.isOpenMap
      (fun t _ => 𝒞.jointly_surjective t)
      U.1.isOpen U.2.isCompact
  exact hcov.exists_mem_of_isBasis (fun i => (𝒞.X i).isBasis_affineOpens)
    fun _ _ hW => hW.isCompact

end FppfCovering

/-- Every fppf covering `𝒞` of a scheme `X` is refined by an fppf covering `𝒲` of `X` whose
index type lies in the universe of `X`, has at most `Scheme.size X` members, and all of
whose members have size at most `Scheme.size X`.

The refinement is assembled from the finite families of affine opens of members of `𝒞`
covering the affine opens of `X` supplied by
`FppfCovering.exists_finite_affineOpens_cover`, so its index type is
`Σ U : X.affineOpens, Fin (n U)`. Each member is an affine open `V` of some `𝒞.X i`, and
the composite `V ⟶ 𝒞.X i ⟶ X` is locally of finite type with `V` quasi-compact, so
`Scheme.size V ≤ Scheme.size X` by Stacks 04T7. -/
lemma exists_small_refinement (X : Scheme.{u}) (𝒞 : FppfCovering.{v} X) :
    ∃ 𝒲 : FppfCovering.{u} X,
      𝒲.IsRefinement 𝒞 ∧
      Cardinal.mk 𝒲.ι ≤ Scheme.size X ∧
      ∀ j, Scheme.size (𝒲.X j) ≤ Scheme.size X := by
  choose n a V hVaff hVcov using 𝒞.exists_finite_affineOpens_cover
  refine ⟨{ ι := Σ U : X.affineOpens, Fin (n U)
            X := fun ⟨U, k⟩ => (V U k).toScheme
            f := fun ⟨U, k⟩ => (V U k).ι ≫ 𝒞.f (a U k)
            flat := fun ⟨U, k⟩ => by have := 𝒞.flat (a U k); infer_instance
            lfp := fun ⟨U, k⟩ => by have := 𝒞.lfp (a U k); infer_instance
            jointly_surjective := ?_ }, fun ⟨U, k⟩ => ⟨a U k, (V U k).ι, rfl⟩, ?_, ?_⟩
  · intro t
    obtain ⟨W, hW, htW, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top t)
    have htU : t ∈ ⋃ k, (𝒞.f (a ⟨W, hW⟩ k)) '' (V ⟨W, hW⟩ k : Set (𝒞.X (a ⟨W, hW⟩ k))) := by
      rw [hVcov ⟨W, hW⟩]; exact htW
    obtain ⟨k, x, hxV, hxt⟩ := Set.mem_iUnion.mp htU
    exact ⟨⟨⟨W, hW⟩, k⟩, ⟨x, hxV⟩, hxt⟩
  · exact Cardinal.mk_sigma_fin_le n X.aleph0_le_size X.mk_affineOpens_le_size
  · rintro ⟨U, k⟩
    have := 𝒞.flat (a U k)
    have := 𝒞.lfp (a U k)
    have : IsAffine (V U k).toScheme := hVaff U k
    exact Scheme.size_le_of_locallyOfFiniteType ((V U k).ι ≫ 𝒞.f (a U k))

/-- **Stacks 0AHL.** Every fppf covering `𝒞` of a scheme `X` is refined by an fppf covering
`𝒲` of `X` indexed in the universe of `X` whose total space is small: the coproduct of the
members of `𝒲` satisfies `Scheme.size (∐ 𝒲.X) ≤ Scheme.size X`. -/
@[stacks 0AHL]
theorem exists_fppf_refinement_schemeSize_le (X : Scheme.{u}) (𝒞 : FppfCovering.{v} X) :
    ∃ 𝒲 : FppfCovering.{u} X,
      𝒲.IsRefinement 𝒞 ∧ Scheme.size (∐ 𝒲.X) ≤ Scheme.size X := by
  obtain ⟨𝒲, href, hcard, hsize⟩ := exists_small_refinement X 𝒞
  exact ⟨𝒲, href,
    schemeSize_coproduct_le 𝒲.X (Scheme.size X) X.aleph0_le_size hcard hsize⟩
