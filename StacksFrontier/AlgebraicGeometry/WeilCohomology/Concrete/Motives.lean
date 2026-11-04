module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Monoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.CanonicalGradedCategory
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubi

/-!
# The category `M_k` of Chow motives

Let `k` be a field. A *Chow motive* over `k` (Stacks Section 0FG9) is a triple `(X, p, m)` with
`X` a smooth projective scheme over `k`, `p ∈ Corr⁰(X, X)` a correspondence with `p ∘ p = p`, and
`m ∈ ℤ`. A morphism `(X, p, m) ⟶ (Y, q, n)` is an element of
`q ∘ Corr^{n-m}(X, Y) ∘ p ⊂ Corr^{n-m}(X, Y)`, and morphisms compose by composition of
correspondences. Stacks 0FGA: these form a `ℚ`-linear category `M_k`, and `h(X) = (X, 1, 0)`,
`h(f) = [Γ_f]` is a contravariant functor from smooth projective schemes over `k` to `M_k`.

The correspondences, their composition and the graph classes are those of the graded category
of correspondences of Stacks 0FG2, `Stacks.WeilCohomology.canonicalCorrespondences_gradedCategory`,
formed with the canonical Gysin classes of the diagonals; associativity of composition
(Stacks 0FG0 (1)), the unit laws of the diagonal (Stacks 0FFD) and the functoriality of graphs
(Stacks 0FG3) are theorems there. `M_k` is the twisted Karoubi envelope
`CategoryTheory.GradedCategory.TwistedKaroubi` of that graded category.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat k`: the category `M_k` of Chow motives over `k`.
* `Stacks.WeilCohomology.ChowMotiveCat.mk'`: the motive `(X, p, m)` of a smooth projective
  scheme `X`, a correspondence `p ∈ Corr⁰(X, X)` with `p ∘ p = p` and an integer `m`.
* `Stacks.WeilCohomology.ChowMotiveCat.projector`: the projector `p ∈ Corr⁰(X, X)` of a motive.
* `Stacks.WeilCohomology.ChowMotiveCat.corrHom`: the subspace
  `q ∘ Corr^{n-m}(X, Y) ∘ p ⊂ Corr^{n-m}(X, Y)`.
* `Stacks.WeilCohomology.ChowMotiveCat.homEquiv`: the morphisms of `M_k` from `(X, p, m)` to
  `(Y, q, n)` are, as a `ℚ`-vector space, `q ∘ Corr^{n-m}(X, Y) ∘ p`.
* `Stacks.WeilCohomology.ChowMotiveCat.linear`: `M_k` is a `ℚ`-linear category.
* `Stacks.WeilCohomology.ChowMotiveCat.h`: the contravariant functor `h`.
* `Stacks.WeilCohomology.ChowMotiveCat.tate`: the Tate motives `𝟏(n) = (Spec k, 1, n)`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.mem_corrHom_iff`: a correspondence of degree `n - m`
  lies in `corrHom` exactly when it is `q ∘ c ∘ p` for some `c ∈ Corr^{n-m}(X, Y)`.
* `Stacks.WeilCohomology.ChowMotiveCat.homEquiv_id` and
  `Stacks.WeilCohomology.ChowMotiveCat.homEquiv_comp`: the identity of `(X, p, m)` is `p`, and
  composition of morphisms of motives is composition of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.h_obj_projector`,
  `Stacks.WeilCohomology.ChowMotiveCat.h_obj_twist` and
  `Stacks.WeilCohomology.ChowMotiveCat.homEquiv_h_map`: `h(X) = (X, 1, 0)` and `h(f) = [Γ_f]`.

## Implementation notes

Morphisms of correspondences in the category of Stacks 0FG2 are elements of the total module
`⨁ᵣ Corrʳ(X, Y)`, and composition adds degrees. The degrees `(n - m) + (p - n)` and `p - m` are
equal integers but not the same type index, so the statements comparing correspondences of such
degrees are made after `DirectSum.of` into the total module, as in
`Stacks.WeilCohomology.GradedCompositionData`; `DirectSum.of` is injective in each degree.

## References

* [Stacks Project, Section 0FG9](https://stacks.math.columbia.edu/tag/0FG9)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.GradedCategory MonoidalCategory

universe u

namespace Stacks.WeilCohomology

variable (k : Type u) [Field k]

/-- The category `M_k` of Chow motives over `k`. An object is a triple `(X, p, m)` of a smooth
projective scheme `X` over `k`, a projector `p ∈ Corr⁰(X, X)` (`p ∘ p = p`) and a twist `m ∈ ℤ`;
a morphism `(X, p, m) ⟶ (Y, q, n)` is a correspondence in `q ∘ Corr^{n-m}(X, Y) ∘ p`, and
composition is composition of correspondences. -/
@[stacks 0FGA "the category M_k of Chow motives (X, p, m) over k"]
abbrev ChowMotiveCat : Type (u + 1) :=
  TwistedKaroubi ℚ (canonicalCorrespondenceCompositionData k).Obj

namespace ChowMotiveCat

variable {k}

/-- The smooth projective scheme `X` of a motive `(X, p, m)`. -/
abbrev scheme (M : ChowMotiveCat k) : (SmoothProjectiveScheme k).FullSubcategory :=
  M.X.as

/-- A morphism of the category of correspondences homogeneous of degree `r`: the image of
`Corrʳ(X, Y)` in the total module `⨁ᵣ Corrʳ(X, Y)`. -/
abbrev homOf {X Y : (SmoothProjectiveScheme k).FullSubcategory} (r : ℤ) :
    SmoothProjectiveCorr X Y r →ₗ[ℚ]
      ((GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
        GradedCompositionData.Obj.mk Y) :=
  DirectSum.lof ℚ ℤ (fun i ↦ SmoothProjectiveCorr X Y i) r

/-- The map `Corrʳ(X, Y) → ⨁ᵣ Corrʳ(X, Y)` is injective. -/
theorem homOf_injective {X Y : (SmoothProjectiveScheme k).FullSubcategory} (r : ℤ) :
    Function.Injective (homOf (X := X) (Y := Y) r) :=
  DirectSum.of_injective (β := fun i ↦ SmoothProjectiveCorr X Y i) r

/-- The degree-`r` component of a morphism of the category of correspondences. -/
abbrev component {X Y : (SmoothProjectiveScheme k).FullSubcategory} (r : ℤ) :
    ((GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
        GradedCompositionData.Obj.mk Y) →ₗ[ℚ] SmoothProjectiveCorr X Y r :=
  DirectSum.component ℚ ℤ (fun i ↦ SmoothProjectiveCorr X Y i) r

/-- A morphism of the category of correspondences is homogeneous of degree `r` exactly when it
is the image of some `c ∈ Corrʳ(X, Y)`. -/
theorem mem_grade_iff {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    {a : (GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
        GradedCompositionData.Obj.mk Y} :
    a ∈ grade (R := ℚ) _ _ r ↔ ∃ c : SmoothProjectiveCorr X Y r, homOf r c = a := by
  rw [GradedCompositionData.mem_grade_iff]
  exact Iff.rfl

/-- The image of `c ∈ Corrʳ(X, Y)` is homogeneous of degree `r`. -/
theorem homOf_mem_grade {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    (c : SmoothProjectiveCorr X Y r) :
    homOf r c ∈ grade (R := ℚ) _ _ r :=
  mem_grade_iff.2 ⟨c, rfl⟩

/-- A morphism homogeneous of degree `r` is the image of its degree-`r` component. -/
theorem homOf_component {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    {a : (GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
        GradedCompositionData.Obj.mk Y} (ha : a ∈ grade (R := ℚ) _ _ r) :
    homOf r (component r a) = a := by
  obtain ⟨c, rfl⟩ := mem_grade_iff.1 ha
  rw [component, DirectSum.component.lof_self]

/-- The degree-`r` component of the image of `c ∈ Corrʳ(X, Y)` is `c`. -/
@[simp]
theorem component_homOf {X Y : (SmoothProjectiveScheme k).FullSubcategory} {r : ℤ}
    (c : SmoothProjectiveCorr X Y r) :
    component r (homOf r c) = c :=
  DirectSum.component.lof_self ℚ r c

/-- Composition of homogeneous morphisms is composition of correspondences: for
`a ∈ Corrʳ(X, Y)` and `b ∈ Corrˢ(Y, Z)` the composite is `b ∘ a ∈ Corr^{r+s}(X, Z)`. -/
theorem homOf_comp_homOf {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {r s : ℤ}
    (a : SmoothProjectiveCorr X Y r) (b : SmoothProjectiveCorr Y Z s) :
    homOf r a ≫ homOf s b =
      homOf (r + s) ((canonicalCorrespondenceCompositionData k).comp a b) := by
  rw [homOf, homOf, homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.lof_eq_of,
    (canonicalCorrespondenceCompositionData k).of_comp_of (X := GradedCompositionData.Obj.mk X)
      (Y := GradedCompositionData.Obj.mk Y) (Z := GradedCompositionData.Obj.mk Z) a b]

/-- The identity of `X` in the category of correspondences is the diagonal class
`[Δ] ∈ Corr⁰(X, X)`. -/
theorem id_eq_homOf (X : (SmoothProjectiveScheme k).FullSubcategory) :
    𝟙 (GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) =
      homOf 0 (correspondenceDiagonal k X) := by
  rw [GradedCompositionData.id_eq, homOf, DirectSum.lof_eq_of]
  rfl

/-! ### Motives as triples -/

/-- The motive `(X, p, m)` of a smooth projective scheme `X` over `k`, a correspondence
`p ∈ Corr⁰(X, X)` with `p ∘ p = p`, and an integer `m`. -/
def mk' (X : (SmoothProjectiveScheme k).FullSubcategory) (p : SmoothProjectiveCorr X X 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p) (m : ℤ) : ChowMotiveCat k where
  X := GradedCompositionData.Obj.mk X
  p := homOf 0 p
  p_mem := homOf_mem_grade p
  idem := by
    rw [homOf_comp_homOf]
    exact congrArg (homOf 0) hp
  twist := m

/-- The projector `p ∈ Corr⁰(X, X)` of a motive `(X, p, m)`. -/
def projector (M : ChowMotiveCat k) : SmoothProjectiveCorr M.scheme M.scheme 0 :=
  component 0 M.p

/-- The image of the projector of `M` in the total module is the idempotent of `M`. -/
theorem homOf_projector (M : ChowMotiveCat k) : homOf 0 M.projector = M.p :=
  homOf_component M.p_mem

/-- The projector of a motive is idempotent as a correspondence: `p ∘ p = p`. -/
theorem projector_comp_projector (M : ChowMotiveCat k) :
    (canonicalCorrespondenceCompositionData k).comp M.projector M.projector = M.projector := by
  apply homOf_injective 0
  show homOf (0 + 0) _ = _
  rw [← homOf_comp_homOf, homOf_projector, M.idem]

/-- The scheme of the motive `(X, p, m)` is `X`. -/
@[simp]
theorem mk'_scheme (X : (SmoothProjectiveScheme k).FullSubcategory) (p : SmoothProjectiveCorr X X 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p) (m : ℤ) :
    (mk' X p hp m).scheme = X :=
  rfl

/-- The projector of the motive `(X, p, m)` is `p`. -/
@[simp]
theorem mk'_projector (X : (SmoothProjectiveScheme k).FullSubcategory)
    (p : SmoothProjectiveCorr X X 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p) (m : ℤ) :
    (mk' X p hp m).projector = p :=
  component_homOf p

/-- The twist of the motive `(X, p, m)` is `m`. -/
@[simp]
theorem mk'_twist (X : (SmoothProjectiveScheme k).FullSubcategory) (p : SmoothProjectiveCorr X X 0)
    (hp : (canonicalCorrespondenceCompositionData k).comp p p = p) (m : ℤ) :
    (mk' X p hp m).twist = m :=
  rfl

/-- Every motive is the triple of its scheme, its projector and its twist. -/
theorem mk'_eta (M : ChowMotiveCat k) :
    mk' M.scheme M.projector (projector_comp_projector M) M.twist = M := by
  obtain ⟨X, p, p_mem, idem, m⟩ := M
  show TwistedKaroubi.mk _ _ _ _ _ = _
  congr
  exact homOf_projector _

/-! ### Morphisms of motives -/

/-- The subspace `q ∘ Corr^{n-m}(X, Y) ∘ p ⊂ Corr^{n-m}(X, Y)` of the correspondences from
`M = (X, p, m)` to `N = (Y, q, n)` of the form `q ∘ c ∘ p`. -/
def corrHom (M N : ChowMotiveCat k) :
    Submodule ℚ (SmoothProjectiveCorr M.scheme N.scheme (N.twist - M.twist)) :=
  (TwistedKaroubi.homSubmodule M N).comap (homOf (N.twist - M.twist))

/-- Equality of correspondences of possibly different degrees, compared after `DirectSum.of`, is
equality of their images in the total module. -/
private theorem of_eq_of_iff_homOf_eq {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {r s : ℤ} (a : SmoothProjectiveCorr X Y r) (b : SmoothProjectiveCorr X Y s) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) r a =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr X Y i) s b ↔ homOf r a = homOf s b :=
  Iff.rfl

/-- The image of `q ∘ c ∘ p` in the total module is `p ≫ c ≫ q`. -/
theorem homOf_comp_comp_projector {M N : ChowMotiveCat k} {r : ℤ}
    (c : SmoothProjectiveCorr M.scheme N.scheme r) :
    homOf (0 + r + 0) ((canonicalCorrespondenceCompositionData k).comp
      ((canonicalCorrespondenceCompositionData k).comp M.projector c) N.projector) =
      M.p ≫ homOf r c ≫ N.p := by
  rw [← homOf_comp_homOf, ← homOf_comp_homOf, homOf_projector, homOf_projector, Category.assoc]

/-- A correspondence `a ∈ Corr^{n-m}(X, Y)` lies in `q ∘ Corr^{n-m}(X, Y) ∘ p` exactly when
`a = q ∘ c ∘ p` for some `c ∈ Corr^{n-m}(X, Y)`; the two sides live in degrees `n - m` and
`(0 + (n - m)) + 0`, and are compared after `DirectSum.of`. -/
theorem mem_corrHom_iff {M N : ChowMotiveCat k}
    {a : SmoothProjectiveCorr M.scheme N.scheme (N.twist - M.twist)} :
    a ∈ corrHom M N ↔ ∃ c : SmoothProjectiveCorr M.scheme N.scheme (N.twist - M.twist),
      DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme N.scheme i) (N.twist - M.twist) a =
        DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme N.scheme i)
          (0 + (N.twist - M.twist) + 0)
          ((canonicalCorrespondenceCompositionData k).comp
            ((canonicalCorrespondenceCompositionData k).comp M.projector c) N.projector) := by
  show homOf _ a ∈ TwistedKaroubi.homSubmodule M N ↔ _
  rw [TwistedKaroubi.mem_homSubmodule_iff]
  constructor
  · rintro ⟨b, hb, hab⟩
    obtain ⟨c, rfl⟩ := mem_grade_iff.1 hb
    refine ⟨c, ?_⟩
    rw [of_eq_of_iff_homOf_eq]
    rw [hab, homOf_comp_comp_projector]
  · rintro ⟨c, hc⟩
    refine ⟨homOf _ c, homOf_mem_grade c, ?_⟩
    rw [of_eq_of_iff_homOf_eq] at hc
    rw [hc, homOf_comp_comp_projector]

/-- The morphisms of `M_k` from `(X, p, m)` to `(Y, q, n)` are the correspondences in
`q ∘ Corr^{n-m}(X, Y) ∘ p ⊂ Corr^{n-m}(X, Y)`: an isomorphism of `ℚ`-vector spaces sending a
morphism to the underlying correspondence. -/
@[stacks 0FGA "Hom((X, p, m), (Y, q, n)) = q o Corr^{n-m}(X, Y) o p, as Q-vector spaces"]
def homEquiv (M N : ChowMotiveCat k) : (M ⟶ N) ≃ₗ[ℚ] corrHom M N where
  toFun f := ⟨component _ f.val, by
    change homOf (N.twist - M.twist) (component (N.twist - M.twist) f.val) ∈
      TwistedKaroubi.homSubmodule M N
    rw [homOf_component f.2.1]
    exact f.2⟩
  invFun c := TwistedKaroubi.Hom.mk (homOf _ c.1) c.2
  left_inv f := TwistedKaroubi.hom_ext (homOf_component f.2.1)
  right_inv c := Subtype.ext (component_homOf c.1)
  map_add' f g := Subtype.ext (map_add (component _) f.val g.val)
  map_smul' r f := Subtype.ext (map_smul (component _) r f.val)

/-- The correspondence of a morphism `f : M ⟶ N` is the degree-`(n - m)` component of `f`. -/
@[simp]
theorem homEquiv_apply_coe {M N : ChowMotiveCat k} (f : M ⟶ N) :
    (homEquiv M N f).1 = component _ f.val :=
  rfl

/-- The image in the total module of the correspondence of `f : M ⟶ N` is the underlying
morphism of `f`. -/
theorem homOf_homEquiv {M N : ChowMotiveCat k} (f : M ⟶ N) :
    homOf _ (homEquiv M N f).1 = f.val :=
  homOf_component f.2.1

/-- The identity morphism of the motive `(X, p, m)` is the projector `p` (compared after
`DirectSum.of`, the degree `m - m` being `0`). -/
@[stacks 0FGA "the identity of (X, p, m) is p"]
theorem homEquiv_id (M : ChowMotiveCat k) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme M.scheme i) (M.twist - M.twist)
        (homEquiv M M (𝟙 M)).1 =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme M.scheme i) 0 M.projector := by
  rw [of_eq_of_iff_homOf_eq]
  rw [homOf_homEquiv, homOf_projector]
  rfl

/-- Composition of morphisms of motives is composition of correspondences: for
`f : (X, p, m) ⟶ (Y, q, n)` and `g : (Y, q, n) ⟶ (Z, r, l)` the correspondence of `f ≫ g` is
`g ∘ f` (compared after `DirectSum.of`, the degrees `l - m` and `(n - m) + (l - n)` being
equal). -/
@[stacks 0FGA "composition of morphisms of motives is composition of correspondences"]
theorem homEquiv_comp {M N P : ChowMotiveCat k} (f : M ⟶ N) (g : N ⟶ P) :
    DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme P.scheme i) (P.twist - M.twist)
        (homEquiv M P (f ≫ g)).1 =
      DirectSum.of (fun i ↦ SmoothProjectiveCorr M.scheme P.scheme i)
        ((N.twist - M.twist) + (P.twist - N.twist))
        ((canonicalCorrespondenceCompositionData k).comp (homEquiv M N f).1
          (homEquiv N P g).1) := by
  rw [of_eq_of_iff_homOf_eq]
  rw [homOf_homEquiv, ← homOf_comp_homOf, homOf_homEquiv, homOf_homEquiv]
  rfl

/-- The category `M_k` of Chow motives is `ℚ`-linear: the morphism spaces are the `ℚ`-vector
spaces `q ∘ Corr^{n-m}(X, Y) ∘ p` and composition is `ℚ`-bilinear, composition of
correspondences being so (Stacks 0FG0 (1)). -/
@[stacks 0FGA "M_k is a Q-linear category"]
abbrev linear : Linear ℚ (ChowMotiveCat k) :=
  TwistedKaroubi.instLinear

/-! ### The functor `h` -/

variable (k)

/-- The contravariant functor `h : {smooth projective schemes over k} ⟶ M_k`,
`h(X) = (X, 1, 0)` with `1 = [Δ_X]` the identity correspondence, and
`h(f) = [Γ_f] ∈ Corr⁰(X, Y)` for `f : Y ⟶ X`. -/
@[stacks 0FGA "the contravariant functor h, h(X) = (X, 1, 0), h(f) = [Gamma_f]"]
def h : ((SmoothProjectiveScheme k).FullSubcategory)ᵒᵖ ⥤ ChowMotiveCat k :=
  TwistedKaroubi.functorOfGrade (canonicalGraphFunctor k) fun f ↦ graphHom_mem_grade f.unop

variable {k}

/-- The degree-`0` component of the identity of `X` is the diagonal class `[Δ] ∈ Corr⁰(X, X)`. -/
private theorem component_id (X : (SmoothProjectiveScheme k).FullSubcategory) :
    component 0 (𝟙 (GradedCompositionData.Obj.mk X :
      (canonicalCorrespondenceCompositionData k).Obj)) = correspondenceDiagonal k X := by
  rw [id_eq_homOf, component_homOf]

/-- The scheme of `h(X)` is `X`. -/
@[simp]
theorem h_obj_scheme (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((h k).obj (Opposite.op X)).scheme = X :=
  rfl

/-- The projector of `h(X)` is `1 = [Δ_X] ∈ Corr⁰(X, X)`. -/
@[stacks 0FGA "h(X) = (X, 1, 0): the projector"]
theorem h_obj_projector (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((h k).obj (Opposite.op X)).projector = correspondenceDiagonal k X := by
  exact component_id X

/-- The twist of `h(X)` is `0`. -/
@[stacks 0FGA "h(X) = (X, 1, 0): the twist"]
theorem h_obj_twist (X : (SmoothProjectiveScheme k).FullSubcategory) :
    ((h k).obj (Opposite.op X)).twist = 0 :=
  rfl

/-- For `f : Y ⟶ X`, the correspondence of `h(f) : h(X) ⟶ h(Y)` is the graph class
`[Γ_f] ∈ Corr⁰(X, Y)`. -/
@[stacks 0FGA "h(f) = [Gamma_f]"]
theorem homEquiv_h_map {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :
    (homEquiv _ _ ((h k).map f.op)).1 = graphCorrespondenceSP f :=
  component_homOf (r := 0) (graphCorrespondenceSP f)

/-! ### Tate motives -/

variable (k)

/-- The Tate motive `𝟏(n) = (Spec k, 1, n)`: the point `Spec k`, the identity correspondence
`1 = [Δ] ∈ Corr⁰(Spec k, Spec k)`, and the twist `n`. -/
def tate (n : ℤ) : ChowMotiveCat k :=
  { TwistedKaroubi.ofObj (R := ℚ)
      (GradedCompositionData.Obj.mk (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) :
        (canonicalCorrespondenceCompositionData k).Obj) with twist := n }

variable {k}

/-- The scheme of `𝟏(n)` is the monoidal unit, the point `Spec k`. -/
@[simp]
theorem tate_scheme (n : ℤ) : (tate k n).scheme = 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) :=
  rfl

/-- The underlying scheme of `𝟏(n)` is `Spec k`. -/
@[simp]
theorem tate_scheme_left (n : ℤ) : (tate k n).scheme.obj.left = AlgebraicGeometry.Spec (.of k) :=
  SmoothProjectiveScheme.tensorUnit_left

/-- The projector of `𝟏(n)` is `1 = [Δ] ∈ Corr⁰(Spec k, Spec k)`. -/
theorem tate_projector (n : ℤ) :
    (tate k n).projector = correspondenceDiagonal k
        (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)) := by
  exact component_id _

/-- The twist of `𝟏(n)` is `n`. -/
@[simp]
theorem tate_twist (n : ℤ) : (tate k n).twist = n :=
  rfl

/-- `𝟏(0) = h(Spec k)`. -/
theorem tate_zero : tate k 0 = (h k).obj
    (Opposite.op (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) :=
  rfl

end ChowMotiveCat

end Stacks.WeilCohomology

end
