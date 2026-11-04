module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Multiplication
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverFieldProperties.OpenImage

/-!
# An open and closed countable union of affines in a group scheme over a field

A group scheme over a field contains an open and closed subscheme which is a countable union of
affine opens.  Such a subscheme is produced as an open subgroup scheme: a quasi-compact open
neighbourhood of the identity which is stable under inversion generates an open subgroup, namely
the union of the images of the multiplication maps of all of its self products over the base, and
an open subgroup scheme of a group scheme over a field is closed.

## Main results

* `AlgebraicGeometry.exists_openSubgroupScheme_isClosed_iUnion_affineOpens`: a group scheme over
  a field has an open and closed subscheme which is a countable union of affine opens.

## Implementation notes

A group scheme over `k` is a group object in the category of schemes over `Spec k`, so the self
products of a subobject are its monoidal powers and the identity section is the unit.  The
subscheme of the conclusion is described by the image of the inclusion of the open subgroup
scheme on underlying topological spaces, and its countable union of affines is given by a
sequence of affine opens: each of the images in question is a quasi-compact open, hence a finite
union of affine opens, and the empty open is affine, so those finite unions can be concatenated
into a single sequence.

The multiplications of several slots are compared through the group structure on the sets of
morphisms to a group object rather than through the monoidal structure, which reduces the
comparison of different bracketings of a self product to the group axioms.

## References

* [Stacks Project, Tag 047U](https://stacks.math.columbia.edu/tag/047U)
* [Stacks Project, Tag 047K](https://stacks.math.columbia.edu/tag/047K)
* [Stacks Project, Tag 047S](https://stacks.math.columbia.edu/tag/047S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

universe u

section Algebra

variable {S : Scheme.{u}} {G A A' B U Q : Over S} [GrpObj G]

/-- A morphism out of a product is the pairing of its two components. -/
private lemma tensorHom_eq_lift {A' B' : Over S} (f : A ⟶ A') (g : B ⟶ B') :
    f ⊗ₘ g = lift (fst A B ≫ f) (snd A B ≫ g) := by
  apply hom_ext <;> simp

/-- Reassociating a product of two multiplications of several slots. -/
private lemma lift_comp_mul_mul (f : A ⟶ G) (h : B ⟶ G) (g : Q ⟶ G) (j : U ⟶ G)
    (φ : A ⊗ B ⟶ Q) (hφ : (fst A B ≫ f) * (snd A B ≫ h) = φ ≫ g) :
    (fst A (B ⊗ U) ≫ f) * (snd A (B ⊗ U) ≫ ((fst B U ≫ h) * (snd B U ≫ j))) =
      (lift (lift (fst A (B ⊗ U)) (snd A (B ⊗ U) ≫ fst B U) ≫ φ)
          (snd A (B ⊗ U) ≫ snd B U)) ≫ ((fst Q U ≫ g) * (snd Q U ≫ j)) := by
  rw [MonObj.comp_mul, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.assoc]
  rw [← hφ, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.assoc]
  rw [mul_assoc]

/-- The inverse of a multiplication of several slots multiplies the inverted slots in the
reverse order. -/
private lemma mul_comp_inv (f : A ⟶ G) (j : U ⟶ G) (invU : U ⟶ U) (ψ : A ⟶ A') (g : A' ⟶ G)
    (φ : U ⊗ A' ⟶ Q) (h : Q ⟶ G)
    (hinv : invU ≫ j = j ≫ ι[G]) (hψ : f ≫ ι[G] = ψ ≫ g)
    (hφ : (fst U A' ≫ j) * (snd U A' ≫ g) = φ ≫ h) :
    ((fst A U ≫ f) * (snd A U ≫ j)) ≫ ι[G] =
      (lift (snd A U ≫ invU) (fst A U ≫ ψ) ≫ φ) ≫ h := by
  have hj : (snd A U ≫ j)⁻¹ = snd A U ≫ invU ≫ j := by
    rw [← GrpObj.comp_inv, CategoryTheory.Hom.inv_def, ← hinv]
  have hf : (fst A U ≫ f)⁻¹ = fst A U ≫ ψ ≫ g := by
    rw [← GrpObj.comp_inv, CategoryTheory.Hom.inv_def, hψ]
  have key : ((fst A U ≫ f) * (snd A U ≫ j)) ≫ ι[G] =
      (snd A U ≫ invU ≫ j) * (fst A U ≫ ψ ≫ g) := by
    rw [← CategoryTheory.Hom.inv_def, mul_inv_rev, hj, hf]
  rw [key, Category.assoc, ← hφ, MonObj.comp_mul]
  simp only [lift_fst_assoc, lift_snd_assoc, Category.assoc]

/-- The `n+1`-fold self product of an object over the base. -/
private noncomputable def tensorPowSucc (U : Over S) : ℕ → Over S
  | 0 => U
  | n + 1 => tensorPowSucc U n ⊗ U

/-- Multiplying together all the slots of the `n+1`-fold self product of a subobject of a
group object. -/
private noncomputable def tensorPowSuccMul (j : U ⟶ G) : (n : ℕ) → (tensorPowSucc U n ⟶ G)
  | 0 => j
  | n + 1 => (fst (tensorPowSucc U n) U ≫ tensorPowSuccMul j n) * (snd (tensorPowSucc U n) U ≫ j)

/-- A product of two multiplications of several slots is again a multiplication of several
slots, up to precomposition. -/
private lemma exists_comp_tensorPowSuccMul (j : U ⟶ G) (a : ℕ) : ∀ b : ℕ, ∃ (p : ℕ)
    (φ : tensorPowSucc U a ⊗ tensorPowSucc U b ⟶ tensorPowSucc U p),
    (fst (tensorPowSucc U a) (tensorPowSucc U b) ≫ tensorPowSuccMul j a) *
      (snd (tensorPowSucc U a) (tensorPowSucc U b) ≫ tensorPowSuccMul j b) =
    φ ≫ tensorPowSuccMul j p
  | 0 => ⟨a + 1, 𝟙 _, (Category.id_comp (tensorPowSuccMul j (a + 1))).symm⟩
  | b + 1 => by
    obtain ⟨p, φ, hφ⟩ := exists_comp_tensorPowSuccMul j a b
    exact ⟨p + 1, _, lift_comp_mul_mul (tensorPowSuccMul j a) (tensorPowSuccMul j b)
      (tensorPowSuccMul j p) j φ hφ⟩

/-- The inverse of a multiplication of several slots is again a multiplication of several
slots, up to precomposition, as soon as the subobject is stable under inversion. -/
private lemma exists_comp_tensorPowSuccMul_inv (j : U ⟶ G) (invU : U ⟶ U)
    (hinv : invU ≫ j = j ≫ ι[G]) : ∀ n : ℕ, ∃ (p : ℕ) (ψ : tensorPowSucc U n ⟶ tensorPowSucc U p),
    tensorPowSuccMul j n ≫ ι[G] = ψ ≫ tensorPowSuccMul j p
  | 0 => ⟨0, invU, hinv.symm⟩
  | n + 1 => by
    obtain ⟨p, ψ, hψ⟩ := exists_comp_tensorPowSuccMul_inv j invU hinv n
    obtain ⟨q, φ, hφ⟩ := exists_comp_tensorPowSuccMul j 0 p
    exact ⟨q, _, mul_comp_inv (tensorPowSuccMul j n) j invU ψ (tensorPowSuccMul j p) φ
      (tensorPowSuccMul j q) hinv hψ hφ⟩

end Algebra

section Topology

variable {S : Scheme.{u}} {G A B U : Over S} [GrpObj G]

/-- The image of a composite is the image under the second map of the image of the first. -/
private lemma range_comp_left {C : Over S} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range (f ≫ g).left.base = g.left.base '' Set.range f.left.base := by
  rw [Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

/-- The image of a morphism factoring through another is contained in the image of the
latter. -/
private lemma range_subset_of_comp_eq {C : Over S} {f : A ⟶ C} {g : B ⟶ C} (φ : A ⟶ B)
    (h : f = φ ≫ g) : Set.range f.left.base ⊆ Set.range g.left.base := by
  rw [h, range_comp_left]
  exact Set.image_subset_range _ _

/-- The image of a product of two morphisms over the base is the intersection of the preimages
of the two images. -/
private lemma range_lift_comp {A' B' : Over S} (f : A ⟶ A') (g : B ⟶ B') :
    Set.range (lift (fst A B ≫ f) (snd A B ≫ g)).left.base =
      (pullback.fst A'.hom B'.hom).base ⁻¹' Set.range f.left.base ∩
        (pullback.snd A'.hom B'.hom).base ⁻¹' Set.range g.left.base := by
  rw [tensorHom_eq_lift f g |>.symm, Over.tensorHom_left]
  exact Scheme.Pullback.range_map _ _ A'.hom B'.hom f.left g.left (𝟙 _) (by simp) (by simp)

/-- The image of the product of two morphisms to a group object is the image under
multiplication of the product of the two images. -/
private lemma range_mul (f : A ⟶ G) (g : B ⟶ G) :
    Set.range ((fst A B ≫ f) * (snd A B ≫ g)).left.base =
      μ[G].left.base '' ((pullback.fst G.hom G.hom).base ⁻¹' Set.range f.left.base ∩
        (pullback.snd G.hom G.hom).base ⁻¹' Set.range g.left.base) := by
  rw [CategoryTheory.Hom.mul_def, range_comp_left, range_lift_comp]

/-- A morphism whose image lies in an open subscheme of the target factors through it. -/
private lemma exists_comp_homMk_opens {X T : Over S} (W : X.left.Opens) (f : T ⟶ X)
    (hf : Set.range f.left.base ⊆ (W : Set X.left)) :
    ∃ g : T ⟶ Over.mk (W.ι ≫ X.hom), g ≫ Over.homMk W.ι = f := by
  have hr : Set.range f.left.base ⊆ Set.range W.ι.base := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨Over.homMk (IsOpenImmersion.lift W.ι f.left hr) ?_, ?_⟩
  · calc IsOpenImmersion.lift W.ι f.left hr ≫ (W.ι ≫ X.hom)
        = (IsOpenImmersion.lift W.ι f.left hr ≫ W.ι) ≫ X.hom := by rw [Category.assoc]
      _ = f.left ≫ X.hom := by rw [IsOpenImmersion.lift_fac]
      _ = T.hom := Over.w f
  · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)

end Topology

section Field

variable {k : Type u} [Field k]

/-- The spectrum of a field has a single point. -/
private lemma subsingleton_spec_of_field : Subsingleton (Spec (.of k)) :=
  show Subsingleton (PrimeSpectrum k) from
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr (Field.toIsField k)

/-- A scheme with compact underlying space is quasi-compact over the spectrum of a field. -/
private lemma quasiCompact_of_field {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] :
    QuasiCompact f := by
  have := subsingleton_spec_of_field (k := k)
  refine ⟨fun V hV hV' => ?_⟩
  rcases Set.eq_empty_or_nonempty V with h | ⟨v, hv⟩
  · simp [h]
  · have hV2 : V = Set.univ := Set.eq_univ_of_forall fun x => (Subsingleton.elim x v) ▸ hv
    rw [hV2, Set.preimage_univ]
    exact isCompact_univ

/-- The self products of a quasi-compact object over a field are quasi-compact. -/
private lemma compactSpace_tensorPowSucc (U : Over (Spec (.of k))) [CompactSpace U.left] :
    ∀ n : ℕ, CompactSpace (tensorPowSucc U n).left
  | 0 => ‹_›
  | n + 1 => by
    have := compactSpace_tensorPowSucc U n
    have := quasiCompact_of_field (tensorPowSucc U n).hom
    show CompactSpace ↥(pullback (tensorPowSucc U n).hom U.hom)
    exact inferInstance

/-- The image of a product of two morphisms to a group scheme over a field is open as soon as
both images are. -/
@[sga "3 VIB 4.4" "special case"]
private lemma isOpen_range_mul {G A B : Over (Spec (.of k))} [GrpObj G] (f : A ⟶ G) (g : B ⟶ G)
    (hf : IsOpen (Set.range f.left.base)) (hg : IsOpen (Set.range g.left.base)) :
    IsOpen (Set.range ((fst A B ≫ f) * (snd A B ≫ g)).left.base) := by
  rw [range_mul]
  exact isOpenMap_mul G _ ((hf.preimage (pullback.fst G.hom G.hom).continuous).inter
    (hg.preimage (pullback.snd G.hom G.hom).continuous))

/-- The image of the multiplication of all slots of a self product of an open subobject of a
group scheme over a field is open. -/
@[sga "3 VIB 4.4" "special case"]
private lemma isOpen_range_tensorPowSuccMul {G U : Over (Spec (.of k))} [GrpObj G] (j : U ⟶ G)
    (hU : IsOpen (Set.range j.left.base)) :
    ∀ n : ℕ, IsOpen (Set.range (tensorPowSuccMul j n).left.base)
  | 0 => hU
  | n + 1 => isOpen_range_mul _ _ (isOpen_range_tensorPowSuccMul j hU n) hU

end Field

/-- A countable union of compact open subsets of a scheme is a countable union of affine
opens. -/
private lemma exists_affineOpens_iUnion_eq {X : Scheme.{u}} (T : ℕ → Set X)
    (hc : ∀ n, IsCompact (T n)) (ho : ∀ n, IsOpen (T n)) :
    ∃ V : ℕ → X.Opens, (∀ n, IsAffineOpen (V n)) ∧ (⋃ n, T n) = ⋃ n, (V n : Set X) := by
  choose s hs hT using fun n =>
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hc n, ho n⟩
  let A : Set X.affineOpens := (⋃ n, s n) ∪ {⟨⊥, isAffineOpen_bot X⟩}
  have hA : A.Countable :=
    (Set.countable_iUnion fun n => (hs n).countable).union (Set.countable_singleton _)
  obtain ⟨f, hf⟩ := hA.exists_eq_range ⟨_, Or.inr rfl⟩
  refine ⟨fun n => (f n).1, fun n => (f n).2, ?_⟩
  have h1 : (⋃ n, T n) = ⋃ i ∈ A, (i : Set X) := by
    simp only [A, Set.biUnion_union, Set.mem_singleton_iff]
    simp only [hT, Set.biUnion_iUnion]
    simp
  rw [h1, hf]
  simp

section Main

variable {k : Type u} [Field k]

/-- Starting from a quasi-compact open neighbourhood of the identity which is stable under
inversion, the union of the images of the multiplication maps of all its self products is an
open subgroup scheme, closed in the ambient group scheme and a countable union of affine
opens. -/
private lemma exists_openSubgroupScheme_aux (G : Grp (Over (Spec (.of k))))
    (U : G.X.left.Opens) (hUcpt : IsCompact (U : Set G.X.left))
    (hid : Set.range η[G.X].left.base ⊆ (U : Set G.X.left))
    (hinv : ι[G.X].left.base '' (U : Set G.X.left) ⊆ (U : Set G.X.left)) :
    ∃ (H : OpenSubgroupScheme G) (V : ℕ → G.X.left.Opens),
      IsOpen (Set.range H.ι.hom.hom.left.base) ∧
      IsClosed (Set.range H.ι.hom.hom.left.base) ∧
      Set.range η[G.X].left.base ⊆ Set.range H.ι.hom.hom.left.base ∧
      (∀ n, IsAffineOpen (V n)) ∧
      Set.range H.ι.hom.hom.left.base = ⋃ n, (V n : Set G.X.left) := by
  have hUcs : CompactSpace (Over.mk (U.ι ≫ G.X.hom)).left := isCompact_iff_compactSpace.mp hUcpt
  set Uov : Over (Spec (.of k)) := Over.mk (U.ι ≫ G.X.hom)
  set jU : Uov ⟶ G.X := Over.homMk U.ι
  have hjU : Set.range jU.left.base = (U : Set G.X.left) := Scheme.Opens.range_ι U
  obtain ⟨invU, hinvU⟩ := exists_comp_homMk_opens U (jU ≫ ι[G.X]) (by
    rw [range_comp_left, hjU]
    exact hinv)
  -- the images of the multiplication maps of the self products of `U`
  set T : ℕ → Set G.X.left := fun n => Set.range (tensorPowSuccMul jU n).left.base
  have hTopen : ∀ n, IsOpen (T n) := isOpen_range_tensorPowSuccMul jU (hjU ▸ U.2)
  have hTcpt : ∀ n, IsCompact (T n) := fun n => by
    have := compactSpace_tensorPowSucc Uov n
    exact isCompact_range (tensorPowSuccMul jU n).left.continuous
  have hT0 : T 0 = (U : Set G.X.left) := hjU
  have hTsub : ∀ n, T n ⊆ ⋃ m, T m := fun n => Set.subset_iUnion T n
  -- the open subscheme they cover
  set W : G.X.left.Opens := ⟨⋃ n, T n, isOpen_iUnion hTopen⟩
  set jW : Over.mk (W.ι ≫ G.X.hom) ⟶ G.X := Over.homMk W.ι
  have hj : Set.range jW.left.base = ⋃ n, T n := Scheme.Opens.range_ι W
  have hidW : Set.range η[G.X].left.base ⊆ ⋃ n, T n := hid.trans (hT0 ▸ hTsub 0)
  -- the identity, the multiplication and the inverse all factor through it
  obtain ⟨eH, heH⟩ := exists_comp_homMk_opens W η[G.X] hidW
  obtain ⟨iH, hiH⟩ := exists_comp_homMk_opens W (jW ≫ ι[G.X]) (by
    rintro x ⟨z, rfl⟩
    obtain ⟨n, w, hw⟩ := Set.mem_iUnion.mp (hj ▸ Set.mem_range_self z)
    obtain ⟨p, ψ, hψ⟩ := exists_comp_tensorPowSuccMul_inv jU invU hinvU n
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    have hx : (tensorPowSuccMul jU n ≫ ι[G.X]).left.base w =
        (jW ≫ ι[G.X]).left.base z := by
      rw [Over.comp_left, Scheme.Hom.comp_apply, Over.comp_left, Scheme.Hom.comp_apply, hw]
    exact range_subset_of_comp_eq ψ hψ ⟨w, hx⟩)
  obtain ⟨mH, hmH⟩ := exists_comp_homMk_opens W
      ((fst (Over.mk (W.ι ≫ G.X.hom)) (Over.mk (W.ι ≫ G.X.hom)) ≫ jW) *
        (snd (Over.mk (W.ι ≫ G.X.hom)) (Over.mk (W.ι ≫ G.X.hom)) ≫ jW)) (by
    rw [range_mul, hj]
    rintro x ⟨y, ⟨hy1, hy2⟩, rfl⟩
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hy1
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hy2
    obtain ⟨p, φ, hφ⟩ := exists_comp_tensorPowSuccMul jU a b
    obtain ⟨z, hz⟩ : y ∈ Set.range (lift (fst (tensorPowSucc Uov a) (tensorPowSucc Uov b) ≫
        tensorPowSuccMul jU a) (snd (tensorPowSucc Uov a) (tensorPowSucc Uov b) ≫
          tensorPowSuccMul jU b)).left.base := by
      rw [range_lift_comp]
      exact ⟨ha, hb⟩
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    have hx : ((fst (tensorPowSucc Uov a) (tensorPowSucc Uov b) ≫ tensorPowSuccMul jU a) *
        (snd (tensorPowSucc Uov a) (tensorPowSucc Uov b) ≫
          tensorPowSuccMul jU b)).left.base z = μ[G.X].left.base y := by
      rw [CategoryTheory.Hom.mul_def, Over.comp_left, Scheme.Hom.comp_apply, hz]
    exact range_subset_of_comp_eq φ hφ ⟨z, hx⟩)
  -- hence the open subscheme is an open subgroup scheme
  have hopenImm : IsOpenImmersion jW.left := by
    show IsOpenImmersion W.ι
    infer_instance
  obtain ⟨K, ε, hε⟩ := (isOpenSubgroupScheme_iff_factor G jW).mpr
    ⟨⟨eH, heH⟩, ⟨mH, by rw [hmH, CategoryTheory.Hom.mul_def, ← tensorHom_eq_lift]⟩, ⟨iH, hiH⟩⟩
  have hεiso : IsIso ε.hom.left := by
    show IsIso ((Over.forget (Spec (.of k))).map ε.hom)
    infer_instance
  have hsurj : Function.Surjective ε.hom.left.base := ε.hom.left.homeomorph.surjective
  have hrange : Set.range K.ι.hom.hom.left.base = ⋃ n, T n := by
    rw [← hj, hε, range_comp_left, hsurj.range_eq, Set.image_univ]
  obtain ⟨V, hVaff, hVunion⟩ := exists_affineOpens_iUnion_eq T hTcpt hTopen
  refine ⟨K, V, hrange ▸ isOpen_iUnion hTopen, ?_, ?_, hVaff, by rw [hrange, hVunion]⟩
  · exact isClosed_range_of_isOpen K.ι (hrange ▸ isOpen_iUnion hTopen)
  · rwa [hrange]

/-- **Stacks Project, Tag 047U.** A group scheme over a field has an open and closed subscheme
which is a countable union of affine opens; it can be taken to be an open subgroup scheme. -/
@[stacks 047U]
theorem exists_openSubgroupScheme_isClosed_iUnion_affineOpens
    (G : Grp (Over (Spec (.of k)))) :
    ∃ (H : OpenSubgroupScheme G) (V : ℕ → G.X.left.Opens),
      IsOpen (Set.range H.ι.hom.hom.left.base) ∧
      IsClosed (Set.range H.ι.hom.hom.left.base) ∧
      Set.range η[G.X].left.base ⊆ Set.range H.ι.hom.hom.left.base ∧
      (∀ n, IsAffineOpen (V n)) ∧
      Set.range H.ι.hom.hom.left.base = ⋃ n, (V n : Set G.X.left) := by
  have hsub := subsingleton_spec_of_field (k := k)
  have hinvinv : ι[G.X] ≫ ι[G.X] = 𝟙 G.X := by
    calc ι[G.X] ≫ ι[G.X] = ι[G.X]⁻¹ := (CategoryTheory.Hom.inv_def _).symm
    _ = ((𝟙 G.X)⁻¹)⁻¹ := by rw [GrpObj.inv_eq_inv]
    _ = 𝟙 G.X := inv_inv _
  have hinvinvL : ι[G.X].left ≫ ι[G.X].left = 𝟙 G.X.left := by
    rw [← Over.comp_left, hinvinv, Over.id_left]
  have hιiso : IsIso ι[G.X].left := ⟨⟨ι[G.X].left, hinvinvL, hinvinvL⟩⟩
  have hιinv : ∀ x : G.X.left, ι[G.X].left.base (ι[G.X].left.base x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, hinvinvL]
    simp
  have hιimg : ∀ A : Set G.X.left, ι[G.X].left.base '' (ι[G.X].left.base '' A) = A := fun A => by
    rw [Set.image_image]
    simp [hιinv]
  have hιopen : ∀ A : Set G.X.left, IsOpen A → IsOpen (ι[G.X].left.base '' A) :=
    fun A hA => ι[G.X].left.homeomorph.isOpenMap A hA
  -- an affine open neighbourhood of the identity, enlarged to be stable under inversion
  have hsub' : Subsingleton ↥(𝟙_ (Over (Spec (.of k)))).left := hsub
  let pt : Spec (.of k) := PrimeSpectrum.mk ⊥ inferInstance
  obtain ⟨V, hV⟩ := G.X.left.isBasis_affineOpens.isOpenCover.exists_mem (η[G.X].left.base pt)
  refine exists_openSubgroupScheme_aux G
    ⟨(V.1 : Set G.X.left) ∪ ι[G.X].left.base '' (V.1 : Set G.X.left),
      V.1.2.union (hιopen _ V.1.2)⟩ ?_ ?_ ?_
  · exact V.2.isCompact.union (V.2.isCompact.image ι[G.X].left.continuous)
  · intro x hx
    obtain ⟨p, rfl⟩ := hx
    rw [hsub'.elim p pt]
    exact Set.mem_union_left _ hV
  · show ι[G.X].left.base '' ((V.1 : Set G.X.left) ∪ ι[G.X].left.base '' (V.1 : Set G.X.left))
      ⊆ (V.1 : Set G.X.left) ∪ ι[G.X].left.base '' (V.1 : Set G.X.left)
    rw [Set.image_union, hιimg]
    exact Set.union_subset Set.subset_union_right Set.subset_union_left

end Main

end AlgebraicGeometry

end
