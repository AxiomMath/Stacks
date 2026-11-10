module

public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.StupidTruncationSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.HypercohomologyPullbackMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSheafSystemPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SheafSystemCohomologyColimit

/-!
# Étale hypercohomology of the colimit of a system of complexes over a limit of schemes

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms `f_{i'i}`, and let `(ℱ_i^•, φ_{i'i})` be a system of
complexes of abelian sheaves on the small étale sites of the `X_i`: maps of complexes
`φ_{i'i} : f_{i'i}⁻¹ℱ_i^• ⟶ ℱ_{i'}^•` satisfying the cocycle condition. If the complexes are
uniformly bounded below, `ℱ_i^n = 0` for `n < a` with `a` independent of `i`, then for
`ℱ^• = colim f_i⁻¹ℱ_i^•` the pull back maps induce

`colim_i H^p(X_i, ℱ_i^•) = H^p(X, ℱ^•)` for all `p ∈ ℤ` ([Stacks, Tag 0EZM]),

and consequently, for a scheme `S`, a limit `X = lim X_i` of such schemes over `S` and
`K ∈ D^+(S_étale)`,

`colim_i H^p(X_i, K|_{X_i}) = H^p(X, K|_X)` for all `p ∈ ℤ` ([Stacks, Tag 0GIT]).

## Main definitions

* `Stacks.EtaleCohomology.EtaleComplexSystem`: a system of complexes of abelian sheaves on an
  inverse system of schemes.
* `Stacks.EtaleCohomology.EtaleComplexSystem.term`: the system of its terms in a fixed degree.
* `Stacks.EtaleCohomology.EtaleComplexSystem.truncGE`: the system of its stupid truncations
  `σ^{≥n}`.
* `Stacks.EtaleCohomology.EtaleComplexSystem.single`: a system of sheaves placed in degree `n`.
* `Stacks.EtaleCohomology.EtaleComplexSystem.IsPullbackCocone`: compatibility of a family of maps
  of complexes `f_i⁻¹ℱ_i^• ⟶ ℱ^•` with the transition maps.

## Main results

* `Stacks.EtaleCohomology.EtaleComplexSystem.isSystemColimit_etaleHypercohomologyPullback`:
  [Stacks, Tag 0EZM].
* `Stacks.EtaleCohomology.isSystemColimit_etaleHypercohomologyMap_of_isLimit`:
  [Stacks, Tag 0GIT].

## Implementation notes

The source deduces 0EZM from [Stacks, Tag 09YQ] with the two spectral sequences of the
complexes, and remarks that the stupid truncations give an alternative argument; that is the
argument used here. For a fixed degree `p` one shows, by descending induction on `n`, that the
pull back maps for the truncations `σ^{≥n}ℱ_i^•` are surjective onto `H^q(X, σ^{≥n}ℱ^•)` in the
colimit for `q ≤ p` and injective in the colimit for `q ≤ p + 1`. For `n > p + 1` all these
groups vanish; the step from `n + 1` to `n` is the five lemma
(`CategoryTheory.Limits.IsSystemColimit.exists_eq_of_exact`,
`CategoryTheory.Limits.IsSystemColimit.exists_eq_zero_of_exact`) applied to the long exact
sequences of the short exact sequences `0 ⟶ σ^{≥n+1} ⟶ σ^{≥n} ⟶ ℱ^n[-n] ⟶ 0`, whose third terms
are handled by 09YQ
(`Stacks.EtaleCohomology.EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback`) after
shifting the sheaf to degree zero. At `n = a` the truncation is the complex itself.

The colimit `ℱ^• = colim f_i⁻¹ℱ_i^•` is given, as in 09YQ, by a complex `ℱ^•` on `X` with maps of
complexes `ι_i : f_i⁻¹ℱ_i^• ⟶ ℱ^•` compatible with the transition maps that present every term
`ℱ^n` as the colimit of the `f_i⁻¹ℱ_i^n`; colimits of complexes are computed termwise. The
lower bound of `ℱ^•` is then a consequence. The transition maps need not satisfy
`φ_{ii} = id`: colimits are colimits of systems (`CategoryTheory.Limits.IsSystemColimit`).

Étale hypercohomology is `Stacks.EtaleCohomology.etaleHypercohomology`, morphisms
`ℤ ⟶ K[p]` in the derived category, and pulling back along `f` is
`Stacks.EtaleCohomology.etaleHypercohomologyMap`. For 0GIT the restriction `K|_{X_i}` is the
action of the exact functor `g_i⁻¹` on derived categories, and the transition maps are induced by
the comparisons `f_{i'i}⁻¹ g_i⁻¹ ≅ g_{i'}⁻¹`.

## References

* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
* [Stacks Project, Tag 0GIT](https://stacks.math.columbia.edu/tag/0GIT)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open StacksDraft.StupidTruncation

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Systems of complexes -/

variable {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})

/-- A *system of complexes* of abelian sheaves on an inverse system of schemes `D`: a complex of
abelian sheaves on the small étale site of each member, together with a map of complexes from
the inverse image of the complex at an index to the complex at any larger index, satisfying the
cocycle condition through the comparisons `Stacks.EtaleCohomology.systemPullbackComp`. -/
structure EtaleComplexSystem where
  /-- The complex on the small étale site of each member of the system. -/
  obj : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (smallEtaleTopology (D.obj i)) Ab.{u + 1}) ℤ
  /-- The map from the inverse image of the complex at an index to the complex at a larger
  index. -/
  map : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    ((systemPullback D Ab.{u + 1} a).mapHomologicalComplex _).obj (obj j) ⟶ obj i
  /-- The cocycle condition. -/
  map_comp : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
    (NatIso.mapHomologicalComplex (systemPullbackComp D Ab.{u + 1} a b) _).inv.app (obj k) ≫
        ((systemPullback D Ab.{u + 1} a).mapHomologicalComplex _).map (map b) ≫ map a =
      map (a ≫ b)

namespace EtaleComplexSystem

variable {D} (F : EtaleComplexSystem D)

/-- The system of sheaves formed by the terms of a system of complexes in a fixed degree. -/
@[simps]
def term (n : ℤ) : EtaleSheafSystem D Ab.{u + 1} where
  obj i := (F.obj i).X n
  map a := (F.map a).f n
  map_comp a b := by
    simpa using congrArg (fun φ => φ.f n) (F.map_comp a b)

variable (c : Cone D)

/-- The compatibility of a family of maps of complexes `ι_i : f_i⁻¹ℱ_i^• ⟶ ℱ^•` with the
transition maps of a system of complexes. -/
def IsPullbackCocone {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}
    (ι : ∀ i : Iᵒᵖ,
      ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕) :
    Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    (NatIso.mapHomologicalComplex (conePullbackComp c a) _).inv.app (F.obj j) ≫
      ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).map (F.map a) ≫ ι i = ι j

variable {F c}

/-- In each degree, a cocone of complexes is a cocone of the system of terms. -/
lemma IsPullbackCocone.term {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) (n : ℤ) :
    LimitHigherDirectImage.IsPullbackCocone c (F.term n) (fun i => (ι i).f n) := fun a => by
  have h := congrArg (fun φ => φ.f n) (hι a)
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f] at h
  exact h

variable (F)

/-- **The pull back maps of a system of complexes compose**, by the cocycle condition. -/
lemma etaleHypercohomologyPullback_map_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (p : ℤ)
    (x : etaleHypercohomology (D.obj k) (DerivedCategory.Q.obj (F.obj k)) p) :
    etaleHypercohomologyPullback (D.map (a ≫ b)) (F.map (a ≫ b)) p x =
      etaleHypercohomologyPullback (D.map a) (F.map a) p
        (etaleHypercohomologyPullback (D.map b) (F.map b) p x) := by
  rw [etaleHypercohomologyPullback_comp (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b),
    ← F.map_comp a b, systemPullbackComp_eq]

/-- **The pull back maps to the limit are compatible with the system.** -/
lemma etaleHypercohomologyPullback_π_comp
    {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℤ)
    (x : etaleHypercohomology (D.obj j) (DerivedCategory.Q.obj (F.obj j)) p) :
    etaleHypercohomologyPullback (c.π.app i) (ι i) p
        (etaleHypercohomologyPullback (D.map a) (F.map a) p x) =
      etaleHypercohomologyPullback (c.π.app j) (ι j) p x := by
  rw [etaleHypercohomologyPullback_comp (c.π.app i) (D.map a) (c.π.app j) (c.w a).symm,
    ← conePullbackComp_eq, hι a]

/-! ### Sheaves placed in one degree, and stupid truncations -/

variable (D) in
/-- A system of sheaves placed in degree `n`, as a system of complexes. -/
abbrev single (G : EtaleSheafSystem D Ab.{u + 1}) (n : ℤ) : EtaleComplexSystem D where
  obj i := (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj (G.obj i)
  map {i j} a := ((systemPullback D Ab.{u + 1} a).mapCochainComplexSingleFunctor n).hom.app
      (G.obj j) ≫ (HomologicalComplex.single _ (ComplexShape.up ℤ) n).map (G.map a)
  map_comp {i j k} a b := by
    apply HomologicalComplex.to_single_hom_ext
    have h := G.map_comp a b
    have hnat := (systemPullbackComp D Ab.{u + 1} a b).inv.naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (G.obj k)).hom
    simp only [Functor.comp_map] at hnat
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
      HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc, ← h,
      ← reassoc_of% hnat]

/-- The cocone of a system of sheaves placed in degree `n`. -/
def singleι (G : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖) (n : ℤ) (i : Iᵒᵖ) :
    ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj ((single D G n).obj i) ⟶
      (HomologicalComplex.single (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1})
        (ComplexShape.up ℤ) n).obj 𝓖 :=
  ((smallEtalePullbackAb (c.π.app i)).mapCochainComplexSingleFunctor n).hom.app (G.obj i) ≫
    (HomologicalComplex.single _ (ComplexShape.up ℤ) n).map (ιG i)

/-- The cocone `singleι G ιG n` of a system of sheaves placed in degree `n` is compatible with the
transition maps when the family `ιG` is. -/
lemma isPullbackCocone_single (G : EtaleSheafSystem D Ab.{u + 1})
    {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖}
    (hιG : LimitHigherDirectImage.IsPullbackCocone c G ιG) (n : ℤ) :
    (single D G n).IsPullbackCocone c (singleι G ιG n) := by
  intro i j a
  apply HomologicalComplex.to_single_hom_ext
  have h := hιG a
  have hnat := (conePullbackComp c a).inv.naturality
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n (G.obj j)).hom
  simp only [Functor.comp_map] at hnat
  simp only [single, singleι, HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc, ← h,
    ← reassoc_of% hnat]
  rfl

/-- The system of stupid truncations `σ^{≥n}ℱ_i^•` of a system of complexes. -/
abbrev truncGE (n : ℤ) : EtaleComplexSystem D where
  obj i := (F.obj i).stupidTrunc (ComplexShape.embeddingUpIntGE n)
  map a := stupidTruncGEMapOfHom (systemPullback D Ab.{u + 1} a) (F.map a) n
  map_comp {i j k} a b := by
    ext m : 1
    by_cases hm : n ≤ m
    · have hF := congrArg (fun φ => φ.f m) (F.map_comp a b)
      have hnat := (systemPullbackComp D Ab.{u + 1} a b).inv.naturality
        (stupidTruncGEXIso (F.obj k) n m hm).hom
      simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
        Functor.mapHomologicalComplex_map_f] at hF
      simp only [Functor.comp_map] at hnat
      simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
        Functor.mapHomologicalComplex_map_f, stupidTruncGEMapOfHom_f _ _ n m hm, Functor.map_comp,
        Category.assoc, Iso.inv_hom_id_map_assoc, ← hF, reassoc_of% hnat]
    · exact (CochainComplex.isZero_of_isStrictlyGE _ n m (by omega)).eq_of_tgt _ _

/-- The transition maps of the system of stupid truncations are the maps induced on stupid
truncations by the transition maps of the system of complexes. -/
@[simp]
lemma truncGE_map (n : ℤ) {i j : Iᵒᵖ} (a : i ⟶ j) :
    (F.truncGE n).map a = stupidTruncGEMapOfHom (systemPullback D Ab.{u + 1} a) (F.map a) n := rfl

/-- The cocone of the stupid truncations. -/
def truncGEι {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (n : ℤ) (i : Iᵒᵖ) :
    ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj ((F.truncGE n).obj i) ⟶
      𝓕.stupidTrunc (ComplexShape.embeddingUpIntGE n) :=
  stupidTruncGEMapOfHom (smallEtalePullbackAb (c.π.app i)) (ι i) n

variable {F} in
/-- If the maps `ι_i : f_i⁻¹ℱ_i^• ⟶ ℱ^•` are compatible with the transition maps, so are the
induced maps `f_i⁻¹σ^{≥n}ℱ_i^• ⟶ σ^{≥n}ℱ^•` of stupid truncations. -/
lemma IsPullbackCocone.truncGE {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) (n : ℤ) : (F.truncGE n).IsPullbackCocone c (F.truncGEι ι n) := by
  intro i j a
  ext m : 1
  by_cases hm : n ≤ m
  · have hF := congrArg (fun φ => φ.f m) (hι a)
    have hnat := (conePullbackComp c a).inv.naturality (stupidTruncGEXIso (F.obj j) n m hm).hom
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplex_map_f] at hF
    simp only [Functor.comp_map] at hnat
    simp only [truncGEι, HomologicalComplex.comp_f,
      NatIso.mapHomologicalComplex_inv_app_f,
      Functor.mapHomologicalComplex_map_f, stupidTruncGEMapOfHom_f _ _ n m hm, Functor.map_comp,
      Category.assoc, Iso.inv_hom_id_map_assoc, ← hF, ← reassoc_of% hnat]
    rfl
  · exact (CochainComplex.isZero_of_isStrictlyGE _ n m (by omega)).eq_of_tgt _ _

/-! ### The two halves of the colimit assertion, and the induction step -/

variable {𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ}

variable (c) in
/-- Every class of `H^q(X, ℱ^•)` comes from a stage: the map from the colimit of the
`H^q(X_i, ℱ_i^•)` is surjective. -/
def HypercohomologySurjective
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (q : ℤ) : Prop :=
  ∀ b : etaleHypercohomology c.pt (DerivedCategory.Q.obj 𝓕) q,
    ∃ (i : Iᵒᵖ) (x : etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (F.obj i)) q),
      etaleHypercohomologyPullback (c.π.app i) (ι i) q x = b

variable (c) in
/-- A class of a stage which vanishes on the limit vanishes at a later stage: the map from the
colimit of the `H^q(X_i, ℱ_i^•)` to `H^q(X, ℱ^•)` is injective. -/
def HypercohomologyInjective
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (q : ℤ) : Prop :=
  ∀ (i : Iᵒᵖ) (x : etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (F.obj i)) q),
    etaleHypercohomologyPullback (c.π.app i) (ι i) q x = 0 →
      ∃ (j : Iᵒᵖ) (a : j ⟶ i), etaleHypercohomologyPullback (D.map a) (F.map a) q x = 0

section Step

variable [IsDirected I (· ≤ ·)]
  {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}

/-- **The induction step, surjectivity.** -/
theorem hypercohomologySurjective_truncGE (hι : F.IsPullbackCocone c ι) (n q : ℤ)
    (h₂ : (F.truncGE (n + 1)).HypercohomologySurjective c (F.truncGEι ι (n + 1)) q)
    (h₄ : (single D (F.term n) n).HypercohomologySurjective c
      (singleι (F.term n) (fun i => (ι i).f n) n) q)
    (h₅ : (F.truncGE (n + 1)).HypercohomologyInjective c (F.truncGEι ι (n + 1)) (q + 1)) :
    (F.truncGE n).HypercohomologySurjective c (F.truncGEι ι n) q := by
  let S := fun i => stupidTruncGEShortComplex (F.obj i) n
  have hS := fun i => stupidTruncGEShortComplex_shortExact (F.obj i) n
  let S' := stupidTruncGEShortComplex 𝓕 n
  have hS' := stupidTruncGEShortComplex_shortExact 𝓕 n
  let ψ := fun {i j : Iᵒᵖ} (a : i ⟶ j) =>
    stupidTruncGEShortComplexMapOfHom (systemPullback D Ab.{u + 1} a) (F.map a) n
  let ψ' := fun i : Iᵒᵖ => stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (c.π.app i))
    (ι i) n
  intro b
  exact IsSystemColimit.exists_eq_of_exact
    (A₂ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₁) q))
    (A₃ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₂) q))
    (A₄ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₃) q))
    (A₅ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₁) (q + 1)))
    (T₃ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₂ q))
    (T₄ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₃ q))
    (T₅ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₁ (q + 1)))
    (B₂ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₁) q))
    (B₃ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₂) q))
    (B₄ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₃) q))
    (B₅ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₁) (q + 1)))
    (ψ₂ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₁ q))
    (ψ₃ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₂ q))
    (ψ₄ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₃ q))
    (ψ₅ := fun i => AddCommGrpCat.ofHom
      (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₁ (q + 1)))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map (S i).f) q))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map (S i).g) q))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyδ (hS i) q (q + 1) (add_comm 1 q)))
    (AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map S'.f) q))
    (AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map S'.g) q))
    (AddCommGrpCat.ofHom (etaleHypercohomologyδ hS' q (q + 1) (add_comm 1 q)))
    (fun a x => (etaleHypercohomologyPullback_comp_triangleOfSESδ _ (hS _) (hS _) (ψ a) _ x).symm)
    (fun a x => (F.truncGE n).etaleHypercohomologyPullback_π_comp (hι.truncGE n) a q x)
    (fun a x => (single D (F.term n) n).etaleHypercohomologyPullback_π_comp
      (isPullbackCocone_single (F.term n) (hι.term n) n) a q x)
    (fun i x => etaleHypercohomologyPullback_comp_Q_map_f _ (ψ' i) q x)
    (fun i x => etaleHypercohomologyPullback_comp_Q_map_g _ (ψ' i) q x)
    (fun i x => (etaleHypercohomologyPullback_comp_triangleOfSESδ _ (hS i) hS' (ψ' i)
      (add_comm 1 q) x).symm)
    (fun i x hx => Pretriangulated.Triangle.shiftedHom_exact₃ _
      (DerivedCategory.triangleOfSES_distinguished (hS i)) _ x hx)
    (fun b hb => Pretriangulated.Triangle.shiftedHom_exact₂ _
      (DerivedCategory.triangleOfSES_distinguished hS') b hb)
    (fun b => Pretriangulated.Triangle.shiftedHom_comp_mor₂_comp_mor₃ _
      (DerivedCategory.triangleOfSES_distinguished hS') _ b)
    h₂ h₄ h₅ b

/-- **The induction step, injectivity.** -/
theorem hypercohomologyInjective_truncGE (hι : F.IsPullbackCocone c ι) (n q : ℤ)
    (h₁ : (single D (F.term n) n).HypercohomologySurjective c
      (singleι (F.term n) (fun i => (ι i).f n) n) (q - 1))
    (h₂ : (F.truncGE (n + 1)).HypercohomologyInjective c (F.truncGEι ι (n + 1)) q)
    (h₄ : (single D (F.term n) n).HypercohomologyInjective c
      (singleι (F.term n) (fun i => (ι i).f n) n) q) :
    (F.truncGE n).HypercohomologyInjective c (F.truncGEι ι n) q := by
  let S := fun i => stupidTruncGEShortComplex (F.obj i) n
  have hS := fun i => stupidTruncGEShortComplex_shortExact (F.obj i) n
  let S' := stupidTruncGEShortComplex 𝓕 n
  have hS' := stupidTruncGEShortComplex_shortExact 𝓕 n
  let ψ := fun {i j : Iᵒᵖ} (a : i ⟶ j) =>
    stupidTruncGEShortComplexMapOfHom (systemPullback D Ab.{u + 1} a) (F.map a) n
  let ψ' := fun i : Iᵒᵖ => stupidTruncGEShortComplexMapOfHom (smallEtalePullbackAb (c.π.app i))
    (ι i) n
  have hq : 1 + (q - 1) = q := by omega
  intro i x hx
  exact IsSystemColimit.exists_eq_zero_of_exact
    (A₁ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₃) (q - 1)))
    (A₂ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₁) q))
    (A₃ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₂) q))
    (A₄ := fun i => AddCommGrpCat.of
      (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (S i).X₃) q))
    (T₁ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₃ (q - 1)))
    (T₂ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₁ q))
    (T₃ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₂ q))
    (T₄ := fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (ψ a).τ₃ q))
    (B₁ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₃) (q - 1)))
    (B₂ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₁) q))
    (B₃ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₂) q))
    (B₄ := AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj S'.X₃) q))
    (ψ₁ := fun i => AddCommGrpCat.ofHom
      (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₃ (q - 1)))
    (ψ₂ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₁ q))
    (ψ₃ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₂ q))
    (ψ₄ := fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ψ' i).τ₃ q))
    (fun a b => by
      ext y
      exact (F.truncGE n).etaleHypercohomologyPullback_map_comp a b q y)
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyδ (hS i) (q - 1) q hq))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map (S i).f) q))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map (S i).g) q))
    (AddCommGrpCat.ofHom (etaleHypercohomologyδ hS' (q - 1) q hq))
    (AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map S'.f) q))
    (AddCommGrpCat.ofHom (etaleHypercohomologyPostcomp (DerivedCategory.Q.map S'.g) q))
    (fun a y => (etaleHypercohomologyPullback_comp_triangleOfSESδ _ (hS _) (hS _) (ψ a) hq y).symm)
    (fun a y => etaleHypercohomologyPullback_comp_Q_map_f _ (ψ a) q y)
    (fun a y => etaleHypercohomologyPullback_comp_Q_map_g _ (ψ a) q y)
    (fun a y => (F.truncGE (n + 1)).etaleHypercohomologyPullback_π_comp (hι.truncGE (n + 1)) a q y)
    (fun a y => (F.truncGE n).etaleHypercohomologyPullback_π_comp (hι.truncGE n) a q y)
    (fun i y => (etaleHypercohomologyPullback_comp_triangleOfSESδ _ (hS i) hS' (ψ' i) hq y).symm)
    (fun i y => etaleHypercohomologyPullback_comp_Q_map_f _ (ψ' i) q y)
    (fun i y => etaleHypercohomologyPullback_comp_Q_map_g _ (ψ' i) q y)
    (fun i y => Pretriangulated.Triangle.shiftedHom_comp_mor₃_comp_mor₁ _
      (DerivedCategory.triangleOfSES_distinguished (hS i)) hq y)
    (fun i y hy => Pretriangulated.Triangle.shiftedHom_exact₂ _
      (DerivedCategory.triangleOfSES_distinguished (hS i)) y hy)
    (fun b hb => Pretriangulated.Triangle.shiftedHom_exact₁ _
      (DerivedCategory.triangleOfSES_distinguished hS') hq b hb)
    h₁ h₂ h₄ i x hx

end Step

/-! ### The system of hypercohomology groups -/

section Colimit

variable {F}

variable (F c) in
/-- The assertion of Stacks 0EZM in degree `p` for a system of complexes `F` and a family `ι` of
maps of complexes `f_i⁻¹ℱ_i^• ⟶ ℱ^•`: the pull back maps exhibit `H^p(X, ℱ^•)` as the colimit of
the system of the `H^p(X_i, ℱ_i^•)`. -/
abbrev IsHypercohomologyColimit
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (p : ℤ) : Prop :=
  IsSystemColimit
    (fun i => AddCommGrpCat.of (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (F.obj i)) p))
    (fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (F.map a) p))
    (AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj 𝓕) p))
    (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ι i) p))

variable (F) in
/-- The pull back maps on hypercohomology along the transition maps of a system of complexes
compose: the map for `a ≫ b` is the map for `b` followed by the map for `a`. -/
lemma ofHom_etaleHypercohomologyPullback_map_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (p : ℤ) :
    AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map (a ≫ b)) (F.map (a ≫ b)) p) =
      AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map b) (F.map b) p) ≫
        AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (F.map a) p) := by
  ext x
  exact F.etaleHypercohomologyPullback_map_comp a b p x

/-- For a compatible family `ι`, the pull back map `H^p(X_j, ℱ_j^•) ⟶ H^p(X_i, ℱ_i^•)` followed by
the pull back map to `H^p(X, ℱ^•)` along `ι_i` is the pull back map along `ι_j`. -/
lemma ofHom_etaleHypercohomologyPullback_π_comp
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℤ) :
    AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (F.map a) p) ≫
        AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ι i) p) =
      AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app j) (ι j) p) := by
  ext x
  exact F.etaleHypercohomologyPullback_π_comp hι a p x

variable [IsDirected I (· ≤ ·)] [Nonempty I]

/-- The colimit assertion in a degree gives both of its halves. -/
lemma IsHypercohomologyColimit.surjective_injective
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) {p : ℤ} (h : F.IsHypercohomologyColimit c ι p) :
    F.HypercohomologySurjective c ι p ∧ F.HypercohomologyInjective c ι p :=
  ⟨fun b => h.exists_eq (F.ofHom_etaleHypercohomologyPullback_map_comp · · p)
      (ofHom_etaleHypercohomologyPullback_π_comp hι · p) b,
    fun _i x hx => h.exists_eq_zero (F.ofHom_etaleHypercohomologyPullback_map_comp · · p)
      (ofHom_etaleHypercohomologyPullback_π_comp hι · p) x hx⟩

omit [Nonempty I] in
/-- Conversely, its two halves give the colimit assertion. -/
lemma isHypercohomologyColimit_of_surjective_of_injective
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι) {p : ℤ} (hs : F.HypercohomologySurjective c ι p)
    (hi : F.HypercohomologyInjective c ι p) : F.IsHypercohomologyColimit c ι p :=
  IsSystemColimit.of_forall_exists.{u, u + 2} (F.ofHom_etaleHypercohomologyPullback_map_comp · · p)
    (ofHom_etaleHypercohomologyPullback_π_comp hι · p) hs hi

omit [IsDirected I (· ≤ ·)] in
/-- Below the degrees of a uniformly bounded below system both halves hold trivially. -/
lemma surjective_injective_of_isStrictlyGE
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (n : ℤ) [∀ i, (F.obj i).IsStrictlyGE n] [𝓕.IsStrictlyGE n] {p : ℤ} (hp : p < n) :
    F.HypercohomologySurjective c ι p ∧ F.HypercohomologyInjective c ι p :=
  ⟨fun _ => ⟨Classical.arbitrary _, 0,
      (subsingleton_etaleHypercohomology_of_isStrictlyGE 𝓕 n p hp).elim _ _⟩,
    fun i _ _ => ⟨i, 𝟙 i,
      (subsingleton_etaleHypercohomology_of_isStrictlyGE (F.obj i) n p hp).elim _ _⟩⟩

end Colimit

/-! ### Sheaves placed in one degree: Stacks 09YQ -/

section Single

variable [IsDirected I (· ≤ ·)] [Nonempty I] (G : EtaleSheafSystem D Ab.{u + 1})
  {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
  {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖}
  (hιG : LimitHigherDirectImage.IsPullbackCocone c G ιG)

include hιG

/-- Shifting a system of sheaves from degree `n` to degree `m = n + 1` preserves the colimit
assertion, in the degrees `p` and `1 + p`. -/
lemma isHypercohomologyColimit_single_iff (n m : ℤ) (h : 1 + n = m) (p q : ℤ) (hpq : 1 + p = q) :
    (single D G n).IsHypercohomologyColimit c (singleι G ιG n) p ↔
      (single D G m).IsHypercohomologyColimit c (singleι G ιG m) q := by
  let e := fun i => etaleHypercohomologySingleShiftAddEquiv (G.obj i) n m h p q hpq
  let eB := etaleHypercohomologySingleShiftAddEquiv 𝓖 n m h p q hpq
  have he : ∀ {i j : Iᵒᵖ} (a : i ⟶ j) x, e i (etaleHypercohomologyPullback (D.map a)
      ((single D G n).map a) p x) = etaleHypercohomologyPullback (D.map a)
        ((single D G m).map a) q (e j x) := fun a x =>
    etaleHypercohomologyPullback_singleShiftAddEquiv (D.map a) (G.map a) n m h p q hpq x
  have heB : ∀ i x, eB (etaleHypercohomologyPullback (c.π.app i) (singleι G ιG n i) p x) =
      etaleHypercohomologyPullback (c.π.app i) (singleι G ιG m i) q (e i x) := fun i x =>
    etaleHypercohomologyPullback_singleShiftAddEquiv (c.π.app i) (ιG i) n m h p q hpq x
  refine ⟨fun hc => IsSystemColimit.of_addEquiv.{u, u + 2, u + 2}
      ((single D G n).ofHom_etaleHypercohomologyPullback_map_comp · · p)
      (ofHom_etaleHypercohomologyPullback_π_comp (isPullbackCocone_single G hιG n) · p) hc
      e eB he heB, fun hc => ?_⟩
  refine IsSystemColimit.of_addEquiv.{u, u + 2, u + 2}
      ((single D G m).ofHom_etaleHypercohomologyPullback_map_comp · · q)
      (ofHom_etaleHypercohomologyPullback_π_comp (isPullbackCocone_single G hιG m) · q) hc
      (fun i => (e i).symm) eB.symm (fun a y => ?_) (fun i y => ?_)
  · exact ((e _).symm_apply_eq).mpr
      ((he a ((e _).symm y)).trans (congrArg _ ((e _).apply_symm_apply y))).symm
  · exact (eB.symm_apply_eq).mpr
      ((heB i ((e _).symm y)).trans (congrArg _ ((e _).apply_symm_apply y))).symm

end Single

section SingleColimit

variable [IsDirected I (· ≤ ·)] [Nonempty I]
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **Stacks 09YQ for a system of sheaves placed in degree zero**, in every degree. -/
lemma isHypercohomologyColimit_single_zero {c : Cone D} (hc : IsLimit c)
    (G : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖}
    (hιG : LimitHigherDirectImage.IsPullbackCocone c G ιG)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 G ιG) (p : ℤ) :
    (single D G 0).IsHypercohomologyColimit c (singleι G ιG 0) p := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨hs, hi⟩ := surjective_injective_of_isStrictlyGE (F := single D G 0)
      (ι := singleι G ιG 0) 0 hp
    exact isHypercohomologyColimit_of_surjective_of_injective
      (isPullbackCocone_single G hιG 0) hs hi
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact IsSystemColimit.of_addEquiv.{u, u + 1, u + 2}
      (fun a b => AddCommGrpCat.ext fun x => G.etaleCohomologyPullback_map_comp a b q x)
      (fun a => AddCommGrpCat.ext fun x => G.etaleCohomologyPullback_π_comp c hιG a q x)
      (EtaleSheafSystem.isSystemColimit_etaleCohomologyPullback hc q G 𝓖 ιG hιG hpres)
      (fun i => etaleHypercohomologySingleAddEquiv (G.obj i) q)
      (etaleHypercohomologySingleAddEquiv 𝓖 q)
      (fun a x =>
        etaleHypercohomologySingleAddEquiv_etaleCohomologyPullback (D.map a) (G.map a) q x)
      (fun i x =>
        etaleHypercohomologySingleAddEquiv_etaleCohomologyPullback (c.π.app i) (ιG i) q x)

/-- **Stacks 09YQ for a system of sheaves placed in any degree `n`**, in every degree. -/
lemma isHypercohomologyColimit_single {c : Cone D} (hc : IsLimit c)
    (G : EtaleSheafSystem D Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}}
    {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (c.π.app i)).obj (G.obj i) ⟶ 𝓖}
    (hιG : LimitHigherDirectImage.IsPullbackCocone c G ιG)
    (hpres : LimitHigherDirectImage.IsPullbackColimitPresentation c 𝓖 G ιG) (n p : ℤ) :
    (single D G n).IsHypercohomologyColimit c (singleι G ιG n) p := by
  induction n using Int.induction_on generalizing p with
  | zero => exact isHypercohomologyColimit_single_zero hc G hιG hpres p
  | succ k ih =>
    exact (isHypercohomologyColimit_single_iff G hιG k (k + 1) (by omega) (p - 1) p
      (by omega)).1 (ih _)
  | pred k ih =>
    exact (isHypercohomologyColimit_single_iff G hιG (-k - 1) (-k) (by omega) p (1 + p)
      rfl).2 (ih _)

end SingleColimit

/-! ### Stacks 0EZM -/

section Main

variable [IsDirected I (· ≤ ·)] [Nonempty I]
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- The colimit of a uniformly bounded below system of complexes is bounded below by the same
bound. -/
lemma isStrictlyGE_of_isPullbackColimitPresentation (a : ℤ) [∀ i, (F.obj i).IsStrictlyGE a]
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hpres : ∀ n, LimitHigherDirectImage.IsPullbackColimitPresentation c (𝓕.X n) (F.term n)
      (fun i => (ι i).f n)) :
    𝓕.IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact (hpres n).isSystemColimit.isZero fun i => Functor.map_isZero _
    (CochainComplex.isZero_of_isStrictlyGE (F.obj i) a n hn)

variable (hc : IsLimit c)

include hc in
/-- The pair of halves of the colimit assertion for the stupid truncations, by descending
induction on the truncation degree. -/
lemma surjective_injective_truncGE (a : ℤ) [∀ i, (F.obj i).IsStrictlyGE a]
    {ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕}
    (hι : F.IsPullbackCocone c ι)
    (hpres : ∀ n, LimitHigherDirectImage.IsPullbackColimitPresentation c (𝓕.X n) (F.term n)
      (fun i => (ι i).f n)) (p : ℤ) :
    (∀ q ≤ p, (F.truncGE a).HypercohomologySurjective c (F.truncGEι ι a) q) ∧
      ∀ q ≤ p + 1, (F.truncGE a).HypercohomologyInjective c (F.truncGEι ι a) q := by
  have hsingle := fun n q => (isHypercohomologyColimit_single hc (F.term n) (hι.term n) (hpres n)
    n q).surjective_injective (isPullbackCocone_single (F.term n) (hι.term n) n)
  refine Int.leInductionDown (m := max (p + 2) a)
    (motive := fun n _ => (∀ q ≤ p, (F.truncGE n).HypercohomologySurjective c (F.truncGEι ι n) q) ∧
      ∀ q ≤ p + 1, (F.truncGE n).HypercohomologyInjective c (F.truncGEι ι n) q) ?_ ?_ a
    (le_max_right _ _)
  · have h := fun q (hq : q < max (p + 2) a) =>
      surjective_injective_of_isStrictlyGE (F := F.truncGE (max (p + 2) a))
        (ι := F.truncGEι ι (max (p + 2) a)) (max (p + 2) a) hq
    exact ⟨fun q hq => (h q (by omega)).1, fun q hq => (h q (by omega)).2⟩
  · intro n _ ih
    rw [show n = n - 1 + 1 by omega] at ih
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · exact F.hypercohomologySurjective_truncGE hι (n - 1) q (ih.1 q hq) (hsingle _ q).1
        (ih.2 (q + 1) (by omega))
    · exact F.hypercohomologyInjective_truncGE hι (n - 1) q (hsingle _ (q - 1)).1 (ih.2 q hq)
        (hsingle _ q).2

include hc in
/-- **Étale cohomology commutes with colimits of bounded below systems of complexes over a limit
of schemes** ([Stacks, Tag 0EZM]). Let `X = lim X_i` be the limit of a directed inverse system of
quasi-compact and quasi-separated schemes with affine transition morphisms, `(ℱ_i^•, φ_{i'i})` a
system of complexes of abelian sheaves on the small étale sites of the `X_i` with `ℱ_i^n = 0` for
`n < a`, `a` independent of `i`, and `ι_i : f_i⁻¹ℱ_i^• ⟶ ℱ^•` maps of complexes, compatible with
the transition maps, which present every term `ℱ^n` as the colimit `colim f_i⁻¹ℱ_i^n`. Then for
every `p ∈ ℤ` the pull back maps `H^p(X_i, ℱ_i^•) ⟶ H^p(X, ℱ^•)` exhibit `H^p(X, ℱ^•)` as the
colimit of the system of the `H^p(X_i, ℱ_i^•)`. -/
@[stacks 0EZM]
theorem isSystemColimit_etaleHypercohomologyPullback (a : ℤ) [∀ i, (F.obj i).IsStrictlyGE a]
    (𝓕 : CochainComplex (Sheaf (smallEtaleTopology c.pt) Ab.{u + 1}) ℤ)
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsPullbackCocone c ι)
    (hpres : ∀ n, LimitHigherDirectImage.IsPullbackColimitPresentation c (𝓕.X n) (F.term n)
      (fun i => (ι i).f n)) (p : ℤ) :
    IsSystemColimit
      (fun i => AddCommGrpCat.of
        (etaleHypercohomology (D.obj i) (DerivedCategory.Q.obj (F.obj i)) p))
      (fun a => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (D.map a) (F.map a) p))
      (AddCommGrpCat.of (etaleHypercohomology c.pt (DerivedCategory.Q.obj 𝓕) p))
      (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyPullback (c.π.app i) (ι i) p)) := by
  have := F.isStrictlyGE_of_isPullbackColimitPresentation a hpres
  obtain ⟨hs, hi⟩ := F.surjective_injective_truncGE hc a hι hpres p
  have hσ := isHypercohomologyColimit_of_surjective_of_injective (hι.truncGE a) (hs p le_rfl)
    (hi p (by omega))
  let e := fun i => etaleHypercohomologyPostcompAddEquiv (DerivedCategory.Q.mapIso
    (asIso (HomologicalComplex.ιStupidTrunc (F.obj i) (ComplexShape.embeddingUpIntGE a)))) p
  let eB := etaleHypercohomologyPostcompAddEquiv (DerivedCategory.Q.mapIso
    (asIso (HomologicalComplex.ιStupidTrunc 𝓕 (ComplexShape.embeddingUpIntGE a)))) p
  refine IsSystemColimit.of_addEquiv.{u, u + 2, u + 2}
    ((F.truncGE a).ofHom_etaleHypercohomologyPullback_map_comp · · p)
    (ofHom_etaleHypercohomologyPullback_π_comp (hι.truncGE a) · p) hσ e eB
    (fun b x => ?_) (fun i x => ?_)
  all_goals
    change etaleHypercohomologyPullback _ _ p x ≫ _ =
      etaleHypercohomologyPullback _ _ p (x ≫ _)
    simp only [Functor.mapIso_hom, asIso_hom]
    rw [etaleHypercohomologyPullback_comp_Q_map, etaleHypercohomologyPullback_Q_map]
    exact congrArg (fun t => etaleHypercohomologyPullback _ t p x)
      (stupidTruncGEMapOfHom_ι _ _ a)

end Main

/-! ### The system of inverse images of one complex -/

section OfCocone

variable {S : Scheme.{u}} (ι : ∀ i, D.obj i ⟶ S)
  (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (G : CochainComplex (Sheaf (smallEtaleTopology S) Ab.{u + 1}) ℤ)

/-- **The system of inverse images of one complex** along a compatible family of morphisms
`ι_i : X_i ⟶ S`: the complex `ι_i⁻¹ G^•` at each index, with the comparisons of inverse images
along composites as transition maps. In each degree it is
`Stacks.EtaleCohomology.EtaleSheafSystem.ofCocone`. -/
def ofCocone : EtaleComplexSystem D where
  obj i := ((smallEtalePullbackAb (ι i)).mapHomologicalComplex _).obj G
  map {i j} a := (NatIso.mapHomologicalComplex
    (smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm) (ComplexShape.up ℤ)).hom.app G
  map_comp {i j k} a b := by
    ext n : 1
    have h := (EtaleSheafSystem.ofCocone ι hι (G.X n)).map_comp a b
    simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
      NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f]
    exact h

variable (c : Cone D) (g : c.pt ⟶ S) (hg : ∀ i, c.π.app i ≫ ι i = g)

/-- The comparisons `f_i⁻¹ ι_i⁻¹ G^• ≅ g⁻¹ G^•` of inverse images along `g = f_i ≫ ι_i`. -/
abbrev ofCoconeLeg (i : Iᵒᵖ) :
    ((smallEtalePullbackAb (c.π.app i)).mapHomologicalComplex _).obj ((ofCocone ι hι G).obj i) ⟶
      ((smallEtalePullbackAb g).mapHomologicalComplex _).obj G :=
  (NatIso.mapHomologicalComplex (smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm)
    (ComplexShape.up ℤ)).hom.app G

/-- The comparisons `f_i⁻¹ ι_i⁻¹ G^• ≅ g⁻¹ G^•` are compatible with the transition maps of the
system of inverse images of `G^•`. -/
lemma isPullbackCocone_ofCocone :
    (ofCocone ι hι G).IsPullbackCocone c (ofCoconeLeg ι hι G c g hg) := by
  intro i j a
  ext n : 1
  have h := EtaleSheafSystem.isPullbackCocone_ofCocone ι hι c g hg (G.X n) a
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    NatIso.mapHomologicalComplex_hom_app_f, Functor.mapHomologicalComplex_map_f]
  exact h

/-- In each degree `n`, the comparisons `f_i⁻¹ ι_i⁻¹ G^n ≅ g⁻¹ G^n` present `g⁻¹ G^n` as the
colimit of the system of inverse images of `G^n`. -/
lemma isPullbackColimitPresentation_ofCocone [IsDirected I (· ≤ ·)] [Nonempty I] (n : ℤ) :
    LimitHigherDirectImage.IsPullbackColimitPresentation c
      ((((smallEtalePullbackAb g).mapHomologicalComplex _).obj G).X n) ((ofCocone ι hι G).term n)
      (fun i => (ofCoconeLeg ι hι G c g hg i).f n) :=
  EtaleSheafSystem.isPullbackColimitPresentation_ofCocone ι hι c g hg (G.X n)

end OfCocone

end EtaleComplexSystem

/-! ### Stacks 0GIT -/

section Restriction

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {S : Scheme.{u}}

include hc in
/-- **Étale cohomology of a bounded below complex pulled back to a limit of schemes**
([Stacks, Tag 0GIT]). Let `S` be a scheme, `X = lim X_i` the limit of a directed inverse system of
quasi-compact and quasi-separated schemes over `S`, with structure morphisms `ι_i : X_i ⟶ S`,
`g : X ⟶ S` and affine transition morphisms, and `K ∈ D^+(S_étale)`. Then for every `p ∈ ℤ` the
pull back maps `H^p(X_i, K|_{X_i}) ⟶ H^p(X, K|_X)` exhibit `H^p(X, K|_X)` as the colimit of the
system of the `H^p(X_i, K|_{X_i})`. Here `K|_{X_i}` is the derived inverse image of `K` along
`ι_i`, and the transition maps are induced by the comparisons `f_{i'i}⁻¹ ι_i⁻¹ ≅ ι_{i'}⁻¹` and
`f_i⁻¹ ι_i⁻¹ ≅ g⁻¹` of inverse images along composites. -/
@[stacks 0GIT]
theorem isSystemColimit_etaleHypercohomologyMap_of_isLimit (ι : ∀ i, D.obj i ⟶ S)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i) (g : c.pt ⟶ S)
    (hg : ∀ i, c.π.app i ≫ ι i = g)
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology S) Ab.{u + 1})) (p : ℤ) :
    IsSystemColimit
      (fun i => AddCommGrpCat.of (etaleHypercohomology (D.obj i)
        ((smallEtalePullbackAb (ι i)).mapDerivedCategory.obj K.obj) p))
      (fun {i j} a => AddCommGrpCat.ofHom (etaleHypercohomologyMap (D.map a)
        ((Functor.mapDerivedCategoryIsoComp _ _ _
          (smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm)).inv.app K.obj) p))
      (AddCommGrpCat.of (etaleHypercohomology c.pt
        ((smallEtalePullbackAb g).mapDerivedCategory.obj K.obj) p))
      (fun i => AddCommGrpCat.ofHom (etaleHypercohomologyMap (c.π.app i)
        ((Functor.mapDerivedCategoryIsoComp _ _ _
          (smallEtalePullbackAbComp' (c.π.app i) (ι i) g (hg i).symm)).inv.app K.obj) p)) := by
  obtain ⟨a, ha⟩ := K.property
  have : K.obj.IsGE a := ha
  obtain ⟨G, _, ⟨eK⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K.obj a
  let F := EtaleComplexSystem.ofCocone ι hι G
  have : ∀ i, (F.obj i).IsStrictlyGE a := fun i =>
    inferInstanceAs
      ((((smallEtalePullbackAb (ι i)).mapHomologicalComplex _).obj G).IsStrictlySupported
        (ComplexShape.embeddingUpIntGE a))
  have h := F.isSystemColimit_etaleHypercohomologyPullback hc a
    (((smallEtalePullbackAb g).mapHomologicalComplex _).obj G)
    (EtaleComplexSystem.ofCoconeLeg ι hι G c g hg)
    (EtaleComplexSystem.isPullbackCocone_ofCocone ι hι G c g hg)
    (EtaleComplexSystem.isPullbackColimitPresentation_ofCocone ι hι G c g hg) p
  -- the identifications `Q(f⁻¹G) ≅ f_D K`
  let θ := fun {T : Scheme.{u}} (f : T ⟶ S) =>
    ((smallEtalePullbackAb f).mapDerivedCategoryFactors.app G).symm ≪≫
      (smallEtalePullbackAb f).mapDerivedCategory.mapIso eK.symm
  have key : ∀ {T T' : Scheme.{u}} (f : T' ⟶ T) (h₁ : T ⟶ S) (h₂ : T' ⟶ S) (hf : h₂ = f ≫ h₁),
      (smallEtalePullbackAb f).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (smallEtalePullbackAbComp' f h₁ h₂ hf) (ComplexShape.up ℤ)).hom.app G) ≫
            (θ h₂).hom =
        (smallEtalePullbackAb f).mapDerivedCategory.map (θ h₁).hom ≫
          (Functor.mapDerivedCategoryIsoComp _ _ _
            (smallEtalePullbackAbComp' f h₁ h₂ hf)).inv.app K.obj := by
    intro T T' f h₁ h₂ hf
    have hn := (Functor.mapDerivedCategoryIsoComp _ _ _
      (smallEtalePullbackAbComp' f h₁ h₂ hf)).inv.naturality eK.inv
    simp only [Functor.comp_map] at hn
    simp only [θ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv, Functor.map_comp,
      Category.assoc]
    rw [hn, Functor.mapDerivedCategoryIsoComp_inv_app_Q]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.assoc]
    exact ((congrArg (· ≫ _) ((smallEtalePullbackAb f).mapDerivedCategory.map_id _)).trans
      (Category.id_comp _)).symm
  refine IsSystemColimit.of_addEquiv.{u, u + 2, u + 2}
    (F.ofHom_etaleHypercohomologyPullback_map_comp · · p)
    (EtaleComplexSystem.ofHom_etaleHypercohomologyPullback_π_comp
      (EtaleComplexSystem.isPullbackCocone_ofCocone ι hι G c g hg) · p) h
    (fun i => etaleHypercohomologyPostcompAddEquiv (θ (ι i)) p)
    (etaleHypercohomologyPostcompAddEquiv (θ g) p) (fun b x => ?_) (fun i x => ?_) <;>
  exact (ShiftedHom.mapAlong_comp_shift_map _ _ _ _ x).trans
    ((congrArg (fun t => ShiftedHom.mapAlong _ _ t x)
      ((Category.assoc _ _ _).trans (key _ _ _ _))).trans
        (ShiftedHom.mapAlong_shift_map _ _ _ _ x).symm)

end Restriction

end Stacks.EtaleCohomology

end
