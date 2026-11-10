module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Formality of complexes whose cohomology is locally concentrated in one degree

Let `X` be a topological space, `R` a sheaf of rings on `X` and `K` a complex of sheaves of
`R`-modules. Suppose that `X` is covered by opens `V i`, each carrying a degree `ℓ i`, such
that over `V i` the cohomology sheaves of `K` vanish outside degree `ℓ i`. Locally `K` is then
quasi-isomorphic to its single nonzero cohomology sheaf placed in degree `ℓ i`. This file turns
the local statement into a global isomorphism `K ≅ ⨁ₖ H^k(K)[-k]` in the derived category, the
right side being realised as the complex of cohomology sheaves with zero differential. It is
assumed that the terms of `K` vanish over `V i ⊓ V j` whenever `ℓ i ≠ ℓ j`. This is the
situation of Stacks Tag 0BQZ, where `R𝓗om(𝒪_X, 𝒪_Y)` is computed locally, in a degree `r` that
is only locally constant.

The isomorphism is a roof of quasi-isomorphisms `K ← L → Z`. Because the terms of `K` vanish on
the overlaps of members of different degrees, each term `K^k` splits as the sum of its parts
living over the members of each degree. `Stacks.SheafOfModules.degreeProj` is the corresponding
family of idempotent endomorphisms, glued from the identity and the zero map on the members of
the cover. The subcomplex `L` has as `k`-th term the sections of `K^k` vanishing over the members
of degree `< k` whose differential vanishes over the members of degree `k`; over a member of
degree `n` this is the good truncation `τ^{≤ n} K`. Sending a section of `L^k` to the class of
its part over the members of degree `≤ k` is a map to the complex `Z` of cohomology sheaves of
`K` with zero differential.

## Main results

* `Stacks.SheafOfModules.nonempty_iso_zeroDifferentialComplex_homology_of_cover`: the
  formality isomorphism in the derived category.
* `Stacks.SheafOfModules.LocallyConcentrated.quasiIso_truncInclusion` and
  `Stacks.SheafOfModules.LocallyConcentrated.quasiIso_truncProj`: the two legs of the roof are
  quasi-isomorphisms.
* `Stacks.SheafOfModules.hom_ext_of_coversTop`: morphisms of sheaves of modules on a site are
  determined by their restrictions to the slices over a family covering the final object.

## Implementation notes

The cover is indexed by an arbitrary type `ι`. Gluing the degree projections uses the gluing of
morphisms of sheaves of modules on a space, which needs an index type in the universe of the
opens of `X`, so the projections are glued over the type `Stacks.SheafOfModules.DegreeCoverIndex`
of pairs `(V i, ℓ i)`.

Quasi-isomorphy of the inclusion `L ⟶ K` is checked over each member of the cover
(`Stacks.SheafOfModules.quasiIso_of_coversTop`), where it is the inclusion of a good truncation
of a complex whose cohomology is concentrated in the truncation degree. Quasi-isomorphy of the
projection `L ⟶ Z` is then deduced globally: on cycles it agrees with the inclusion followed by
the projection onto the cohomology of `K`, because the two differ by the part of a cycle living
over the members of degree `> k`, whose class in `H^k(K)` vanishes over every member of the
cover.

## References

* [Stacks Project, Tag 0BQZ](https://stacks.math.columbia.edu/tag/0BQZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace Stacks.SheafOfModules

section ShortComplex

variable {C : Type*} [Category C] [Abelian C]

/-- A morphism `φ : S₁ ⟶ S₂` of short complexes induces an isomorphism in homology as soon as
`φ.τ₁` is an epimorphism, the second differential of `S₁` vanishes, and `φ.τ₂` is a kernel of
the second differential of `S₂`. -/
theorem isIso_homologyMap_of_isLimit_τ₂ {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (hφ₁ : Epi φ.τ₁) (hg₁ : S₁.g = 0)
    (hφ : IsLimit (KernelFork.ofι φ.τ₂ (by rw [φ.comm₂₃, hg₁, zero_comp] : φ.τ₂ ≫ S₂.g = 0))) :
    IsIso (ShortComplex.homologyMap φ) := by
  have := S₁.isIso_iCycles hg₁
  have : Mono φ.τ₂ := mono_of_isLimit_fork hφ
  have hmono : Mono (ShortComplex.cyclesMap φ) := by
    have : Mono (ShortComplex.cyclesMap φ ≫ S₂.iCycles) := by
      rw [ShortComplex.cyclesMap_i]
      infer_instance
    exact mono_of_mono _ S₂.iCycles
  obtain ⟨u, hu⟩ := KernelFork.IsLimit.lift' hφ S₂.iCycles S₂.iCycles_g
  have hepi : Epi (ShortComplex.cyclesMap φ) := by
    have h : (u ≫ inv S₁.iCycles) ≫ ShortComplex.cyclesMap φ = 𝟙 _ := by
      rw [← cancel_mono S₂.iCycles, Category.assoc, Category.assoc, ShortComplex.cyclesMap_i,
        IsIso.inv_hom_id_assoc, Category.id_comp]
      exact hu
    exact epi_of_epi_fac h
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi (isIso_of_mono_of_epi _) hφ₁

/-- Let `ι : L ⟶ K` be a quasi-isomorphism of cochain complexes and let `π : L ⟶ Z` be a morphism
to a complex with zero differential. If, in every degree, `π` agrees on cycles with the
composite of `ι` and the projection onto the cohomology of `K`, up to an isomorphism
`K.homology k ≅ Z.X k`, then `π` is a quasi-isomorphism. -/
theorem quasiIso_of_iCycles_comp_eq {L K Z : CochainComplex C ℤ} (ι : L ⟶ K) [QuasiIso ι]
    (π : L ⟶ Z) (hZ : ∀ i j, Z.d i j = 0) (e : ∀ k, K.homology k ≅ Z.X k)
    (h : ∀ k, L.iCycles k ≫ π.f k =
      HomologicalComplex.cyclesMap ι k ≫ K.homologyπ k ≫ (e k).hom) :
    QuasiIso π := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let θ : Z.homology k ⟶ Z.X k := (Z.isoHomologyπ (k - 1) k (by simp) (hZ _ _)).inv ≫
    (Z.iCyclesIso k (k + 1) (by simp) (hZ _ _)).hom
  have hθ : HomologicalComplex.homologyMap π k ≫ θ =
      HomologicalComplex.homologyMap ι k ≫ (e k).hom := by
    rw [← cancel_epi (L.homologyπ k), HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality_assoc]
    simp only [θ, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc,
      HomologicalComplex.iCyclesIso_hom, HomologicalComplex.cyclesMap_i, h]
  have : IsIso (HomologicalComplex.homologyMap π k ≫ θ) := by
    rw [hθ]
    infer_instance
  exact IsIso.of_isIso_comp_right _ θ

end ShortComplex

section Site

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- **A morphism of sheaves of modules vanishing on a cover vanishes.** If the restriction of
`h` to the slice site over each member of a family covering the final object is zero, then `h`
is zero: its kernel inclusion is then locally, hence globally, invertible. -/
theorem eq_zero_of_coversTop {ι : Type*} {V : ι → C} (hV : J.CoversTop V)
    {M N : _root_.SheafOfModules.{u} R} (h : M ⟶ N)
    (hh : ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map h = 0) : h = 0 := by
  have hι : ∀ i, IsIso ((_root_.SheafOfModules.overFunctor R (V i)).map (kernel.ι h)) := by
    intro i
    let := LocalCokernel.overFunctor_preservesFiniteLimits (R := R) (V i)
    exact KernelFork.IsLimit.isIso_ι _ (KernelFork.mapIsLimit _ (kernelIsKernel h) _) (hh i)
  have := Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _ hι
  exact zero_of_epi_comp (kernel.ι h) (kernel.condition h)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}] in
/-- **Morphisms of sheaves of modules are determined on a cover.** Two morphisms whose
restrictions to the slice site over each member of a family covering the final object agree
are equal. -/
theorem hom_ext_of_coversTop {ι : Type*} {V : ι → C} (hV : J.CoversTop V)
    {M N : _root_.SheafOfModules.{u} R} {f g : M ⟶ N}
    (h : ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).map f =
      (_root_.SheafOfModules.overFunctor R (V i)).map g) : f = g :=
  sub_eq_zero.1 (eq_zero_of_coversTop hV (f - g) fun i => by
    rw [Functor.map_sub, h i, sub_self])

end Site

section Space

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- A section of a sheaf of modules over an open contained in `U` vanishes as soon as the
restriction of the sheaf to the slice site over `U` is a zero object. -/
theorem eq_zero_of_isZero_overFunctor_obj {M : _root_.SheafOfModules.{u} R} {U : Opens X}
    (h : IsZero ((_root_.SheafOfModules.overFunctor R U).obj M)) {W : Opens X} (hW : W ≤ U)
    (s : M.val.obj (op W)) : s = 0 :=
  congrArg (fun f => (_root_.SheafOfModules.Hom.val f).app (op (Over.mk (homOfLE hW))) s)
    (h.eq_of_src (𝟙 _) 0)

variable {ι : Type*} (V : ι → Opens X) (ℓ : ι → ℤ)

/-- The members of the family `V`, each recorded together with its degree `ℓ i`. Unlike `ι`,
this index type lives in the universe of the opens of `X`. -/
abbrev DegreeCoverIndex : Type u := {p : Opens X × ℤ // ∃ i, V i = p.1 ∧ ℓ i = p.2}

/-- The family of opens indexed by `DegreeCoverIndex V ℓ` covers `X` when `V` does. -/
theorem iSup_degreeCoverIndex (hV : ⨆ i, V i = ⊤) :
    ⨆ p : DegreeCoverIndex V ℓ, p.1.1 = ⊤ := by
  rw [eq_top_iff, ← hV]
  exact iSup_le fun i => le_iSup_of_le (⟨(V i, ℓ i), i, rfl, rfl⟩ : DegreeCoverIndex V ℓ) le_rfl

/-- The local datum of the degree projection: over the member `p` of the cover it is the
identity if the degree of `p` satisfies `P`, and zero otherwise. -/
def degreeProjLocal (M : _root_.SheafOfModules.{u} R) (P : ℤ → Prop) [DecidablePred P]
    (p : DegreeCoverIndex V ℓ) : TopCat.Sheaf.LocalModuleHom M.val M.val p.1.1 where
  app W _ := if P p.1.2 then 𝟙 _ else 0
  naturality := by
    intro W W' hW hW' s
    split_ifs
    · rfl
    · simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

variable {V ℓ} in
/-- The local data of the degree projection agree on overlaps, because the sheaf vanishes on
the overlap of two members of different degrees. -/
theorem degreeProjLocal_app_eq {M : _root_.SheafOfModules.{u} R}
    (hM : ∀ i j, ℓ i ≠ ℓ j → IsZero ((_root_.SheafOfModules.overFunctor R (V i ⊓ V j)).obj M))
    (P : ℤ → Prop) [DecidablePred P] (p q : DegreeCoverIndex V ℓ) (W : Opens X)
    (hp : W ≤ p.1.1) (hq : W ≤ q.1.1) :
    (degreeProjLocal V ℓ M P p).app W hp = (degreeProjLocal V ℓ M P q).app W hq := by
  obtain ⟨⟨U, a⟩, i, hi, ha⟩ := p
  obtain ⟨⟨U', b⟩, j, hj, hb⟩ := q
  simp only at hi ha hj hb hp hq
  subst hi ha hj hb
  by_cases hab : P (ℓ i) ↔ P (ℓ j)
  · simp only [degreeProjLocal, hab]
  · have hne : ℓ i ≠ ℓ j := fun h => hab (by rw [h])
    ext s
    rw [eq_zero_of_isZero_overFunctor_obj (hM i j hne) (le_inf hp hq) s]
    simp

/-- **The degree projection.** Let `M` be a sheaf of modules vanishing on `V i ⊓ V j` whenever
`ℓ i ≠ ℓ j`, and let `P` be a predicate on degrees. Then `M` splits as the part living on the
members of degree satisfying `P` and the rest, and `degreeProj` is the corresponding idempotent
endomorphism of `M`: it restricts to the identity over each `V i` with `P (ℓ i)` and to zero
over the others (`overFunctor_map_degreeProj`). -/
def degreeProj (hV : ⨆ i, V i = ⊤) (M : _root_.SheafOfModules.{u} R)
    (hM : ∀ i j, ℓ i ≠ ℓ j → IsZero ((_root_.SheafOfModules.overFunctor R (V i ⊓ V j)).obj M))
    (P : ℤ → Prop) [DecidablePred P] : M ⟶ M :=
  ⟨TopCat.Sheaf.LocalModuleHom.gluedHom (iSup_degreeCoverIndex V ℓ hV) M.isSheaf
    (degreeProjLocal V ℓ M P) (fun p q W hp hq => degreeProjLocal_app_eq hM P p q W hp hq)⟩

variable {V ℓ}

/-- The restriction of the degree projection to the slice over `V i` is the identity if
`P (ℓ i)` holds and zero otherwise. -/
theorem overFunctor_map_degreeProj (hV : ⨆ i, V i = ⊤) (M : _root_.SheafOfModules.{u} R)
    (hM : ∀ i j, ℓ i ≠ ℓ j → IsZero ((_root_.SheafOfModules.overFunctor R (V i ⊓ V j)).obj M))
    (P : ℤ → Prop) [DecidablePred P] (i : ι) :
    (_root_.SheafOfModules.overFunctor R (V i)).map (degreeProj V ℓ hV M hM P) =
      if P (ℓ i) then 𝟙 _ else 0 := by
  have key : ∀ T : Over (V i), (degreeProj V ℓ hV M hM P).val.app (op T.left) =
      if P (ℓ i) then 𝟙 _ else 0 := fun T =>
    TopCat.Sheaf.LocalModuleHom.gluedHom_app (iSup_degreeCoverIndex V ℓ hV) M.isSheaf
      (degreeProjLocal V ℓ M P) (fun p q W hp hq => degreeProjLocal_app_eq hM P p q W hp hq)
      (⟨(V i, ℓ i), i, rfl, rfl⟩ : DegreeCoverIndex V ℓ) T.left T.hom.le
  split_ifs with hP <;>
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => (key T.unop).trans ?_)
  · exact ite_eq_left hP
  · exact ite_eq_right hP

section Formality

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace LocallyConcentrated

variable (K : CochainComplex (_root_.SheafOfModules.{u} R) ℤ) (hV : ⨆ i, V i = ⊤)
  (hX : ∀ i j k, ℓ i ≠ ℓ j →
    IsZero ((_root_.SheafOfModules.overFunctor R (V i ⊓ V j)).obj (K.X k)))

/-- The degree projection on the `k`-th term of `K`. -/
abbrev proj (k : ℤ) (P : ℤ → Prop) [DecidablePred P] : K.X k ⟶ K.X k :=
  degreeProj V ℓ hV (K.X k) (fun i j h => hX i j k h) P

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction of `proj` to the slice over `V i`. -/
theorem overFunctor_map_proj (k : ℤ) (P : ℤ → Prop) [DecidablePred P] (i : ι) :
    (_root_.SheafOfModules.overFunctor R (V i)).map (proj K hV hX k P) =
      if P (ℓ i) then 𝟙 _ else 0 :=
  overFunctor_map_degreeProj hV _ _ P i

include hV in
omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The family `V` covers the final object of the site of opens. -/
theorem coversTop : (Opens.grothendieckTopology X).CoversTop V :=
  (Opens.coversTop_iff _ V).2 hV

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The degree projections commute with the differentials. -/
@[reassoc]
theorem d_comp_proj (a b : ℤ) (P : ℤ → Prop) [DecidablePred P] :
    K.d a b ≫ proj K hV hX b P = proj K hV hX a P ≫ K.d a b := by
  refine hom_ext_of_coversTop (coversTop hV) fun i => ?_
  simp only [Functor.map_comp, overFunctor_map_proj]
  split_ifs <;> simp

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The degree projection for a predicate which is the disjoint union of two others is the
sum of the two degree projections. -/
theorem proj_eq_add (k : ℤ) (P Q Q' : ℤ → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred Q'] (h : ∀ x, P x ↔ Q x ∨ Q' x) (h' : ∀ x, ¬ (Q x ∧ Q' x)) :
    proj K hV hX k P = proj K hV hX k Q + proj K hV hX k Q' := by
  refine hom_ext_of_coversTop (coversTop hV) fun i => ?_
  rw [Functor.map_add, overFunctor_map_proj, overFunctor_map_proj, overFunctor_map_proj]
  have h1 := h (ℓ i)
  have h2 := h' (ℓ i)
  by_cases hQ : Q (ℓ i) <;> by_cases hQ' : Q' (ℓ i) <;> by_cases hP : P (ℓ i) <;>
    simp_all

/-- The `k`-th term of the local truncation: sections vanishing over the members of degree
`< k` whose differential vanishes over the members of degree `k`. -/
abbrev truncX (k : ℤ) : _root_.SheafOfModules.{u} R :=
  kernel (kernel.ι (proj K hV hX k (· < k)) ≫ K.d k (k + 1) ≫ proj K hV hX (k + 1) (· = k))

/-- The inclusion of the `k`-th term of the local truncation into `K.X k`. -/
def truncι (k : ℤ) : truncX K hV hX k ⟶ K.X k :=
  kernel.ι _ ≫ kernel.ι _

/-- The inclusion of a term of the local truncation is a monomorphism. -/
instance (k : ℤ) : Mono (truncι K hV hX k) := by
  unfold truncι
  infer_instance

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Sections of the local truncation vanish over the members of degree `< k`. -/
@[reassoc]
theorem truncι_proj (k : ℤ) : truncι K hV hX k ≫ proj K hV hX k (· < k) = 0 := by
  simp [truncι]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The differential of a section of the local truncation vanishes over the members of
degree `k`. -/
@[reassoc]
theorem truncι_d_proj (k : ℤ) :
    truncι K hV hX k ≫ K.d k (k + 1) ≫ proj K hV hX (k + 1) (· = k) = 0 := by
  rw [truncι, Category.assoc]
  exact kernel.condition _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The differential of a section of the local truncation vanishes over the members of
degree `< k + 1`, so the differential of `K` preserves the local truncation. -/
theorem truncι_d_proj_lt (k : ℤ) :
    (truncι K hV hX k ≫ K.d k (k + 1)) ≫ proj K hV hX (k + 1) (· < k + 1) = 0 := by
  rw [Category.assoc, d_comp_proj,
    proj_eq_add K hV hX k (· < k + 1) (· < k) (· = k) (fun x => by omega) (fun x => by omega),
    Preadditive.add_comp, Preadditive.comp_add, truncι_proj_assoc, zero_comp, zero_add,
    ← d_comp_proj, truncι_d_proj]

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The part of a section of the local truncation living over the members of degree `≤ k` is a
cycle of `K`. -/
theorem truncι_proj_le_d (k : ℤ) :
    (truncι K hV hX k ≫ proj K hV hX k (· ≤ k)) ≫ K.d k (k + 1) = 0 := by
  rw [Category.assoc, ← d_comp_proj,
    proj_eq_add K hV hX (k + 1) (· ≤ k) (· < k) (· = k) (fun x => by omega) (fun x => by omega),
    Preadditive.comp_add, Preadditive.comp_add, d_comp_proj, truncι_proj_assoc, zero_comp,
    zero_add, truncι_d_proj]

/-- The differential of the local truncation. -/
def truncD (k : ℤ) : truncX K hV hX k ⟶ truncX K hV hX (k + 1) :=
  kernel.lift _ (kernel.lift _ (truncι K hV hX k ≫ K.d k (k + 1)) (truncι_d_proj_lt K hV hX k))
    (by simp)

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The differential of the local truncation is the restriction of the differential of `K`. -/
@[reassoc (attr := simp)]
theorem truncD_ι (k : ℤ) :
    truncD K hV hX k ≫ truncι K hV hX (k + 1) = truncι K hV hX k ≫ K.d k (k + 1) := by
  simp [truncD, truncι]

/-- **The local truncation** of `K`: over a member `V m` of the cover it is the good
truncation of `K` in degrees `≤ ℓ m`. -/
def trunc : CochainComplex (_root_.SheafOfModules.{u} R) ℤ :=
  CochainComplex.of (truncX K hV hX) (truncD K hV hX) fun k => by
    rw [← cancel_mono (truncι K hV hX (k + 1 + 1))]
    simp

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The differential of `trunc` is `truncD`. -/
theorem trunc_d (k : ℤ) : (trunc K hV hX).d k (k + 1) = truncD K hV hX k :=
  CochainComplex.of_d _ _ _

/-- The inclusion of the local truncation into `K`. -/
def truncInclusion : trunc K hV hX ⟶ K where
  f := truncι K hV hX
  comm' := by
    rintro i j rfl
    rw [trunc_d]
    exact (truncD_ι K hV hX i).symm

/-- The `k`-th component of the projection of the local truncation onto the cohomology. -/
def truncProjF (k : ℤ) : truncX K hV hX k ⟶ K.homology k :=
  K.liftCycles (truncι K hV hX k ≫ proj K hV hX k (· ≤ k)) (k + 1) (by simp)
    (truncι_proj_le_d K hV hX k) ≫ K.homologyπ k

/-- The projection of the local truncation onto the complex of cohomology sheaves of `K` with
zero differential. -/
def truncProj : trunc K hV hX ⟶ CochainComplex.zeroDifferentialComplex fun k => K.homology k where
  f := truncProjF K hV hX
  comm' := by
    rintro i j rfl
    rw [trunc_d]
    change truncProjF K hV hX i ≫ 0 = truncD K hV hX i ≫ truncProjF K hV hX (i + 1)
    rw [comp_zero, truncProjF, HomologicalComplex.comp_liftCycles_assoc]
    exact (K.liftCycles_homologyπ_eq_zero_of_boundary _ _ _
      (truncι K hV hX i ≫ proj K hV hX i (· ≤ i + 1))
      (by rw [truncD_ι_assoc, Category.assoc, d_comp_proj])).symm

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Over a member `V m` of the cover, the differential of `truncι` in degree `ℓ m` vanishes. -/
theorem overFunctor_map_truncι_comp_d (m : ι) (k : ℤ) (hk : k = ℓ m) :
    (_root_.SheafOfModules.overFunctor R (V m)).map (truncι K hV hX k) ≫
      (_root_.SheafOfModules.overFunctor R (V m)).map (K.d k (k + 1)) = 0 := by
  have he : (_root_.SheafOfModules.overFunctor R (V m)).map
      (proj K hV hX (k + 1) (· = k)) = 𝟙 _ := by
    rw [overFunctor_map_proj, ite_eq_left hk.symm]
  rw [← Category.comp_id ((_root_.SheafOfModules.overFunctor R (V m)).map (K.d k (k + 1))),
    ← he, ← Functor.map_comp, ← Functor.map_comp, truncι_d_proj, Functor.map_zero]

/-- Over a member `V m` of the cover, the term of the local truncation in degree `ℓ m` is the
kernel of the differential of `K`. -/
def isLimitOverFunctorMapTruncι (m : ι) (k : ℤ) (hk : k = ℓ m) :
    IsLimit (KernelFork.ofι ((_root_.SheafOfModules.overFunctor R (V m)).map (truncι K hV hX k))
      (overFunctor_map_truncι_comp_d K hV hX m k hk)) := by
  letI := LocalCokernel.overFunctor_preservesFiniteLimits (R := R) (V m)
  let F := _root_.SheafOfModules.overFunctor R (V m)
  have hF : ∀ (a : ℤ) (P : ℤ → Prop) [DecidablePred P],
      F.map (proj K hV hX a P) = if P (ℓ m) then 𝟙 _ else 0 :=
    fun a P _ => overFunctor_map_proj K hV hX a P m
  have hA : IsIso (F.map (kernel.ι (proj K hV hX k (· < k)))) :=
    KernelFork.IsLimit.isIso_ι _ (KernelFork.mapIsLimit _ (kernelIsKernel _) F)
      (by rw [hF, ite_eq_right (by omega)])
  let eA := asIso (F.map (kernel.ι (proj K hV hX k (· < k))))
  have hβ : F.map (kernel.ι (proj K hV hX k (· < k)) ≫ K.d k (k + 1) ≫
      proj K hV hX (k + 1) (· = k)) = eA.hom ≫ F.map (K.d k (k + 1)) := by
    simp only [eA, asIso_hom, F.map_comp, hF, ite_eq_left hk.symm, Category.comp_id]
  refine IsLimit.ofIsoLimit (KernelFork.isLimitOfIsLimitOfIff
    (KernelFork.mapIsLimit _ (kernelIsKernel _) F) (F.map (K.d k (k + 1))) eA
    (fun W φ => by rw [hβ])) (Fork.ext (Iso.refl _) ?_)
  change 𝟙 _ ≫ F.map (truncι K hV hX k) = F.map (kernel.ι _) ≫ F.map (kernel.ι _)
  rw [Category.id_comp, truncι, F.map_comp]

variable (hH : ∀ i k, k ≠ ℓ i →
  IsZero ((_root_.SheafOfModules.overFunctor R (V i)).obj (K.homology k)))

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `truncι_proj_le_d`, stated with the components of `truncInclusion`. -/
theorem truncInclusion_f_proj_le_d (k : ℤ) :
    ((truncInclusion K hV hX).f k ≫ proj K hV hX k (· ≤ k)) ≫ K.d k (k + 1) = 0 :=
  truncι_proj_le_d K hV hX k

omit [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
  [∀ W : Opens X,
    ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The components of `truncProj`, stated with the components of `truncInclusion`. -/
theorem truncProj_f (k : ℤ) :
    (truncProj K hV hX).f k = K.liftCycles ((truncInclusion K hV hX).f k ≫
      proj K hV hX k (· ≤ k)) (k + 1) (by simp) (truncInclusion_f_proj_le_d K hV hX k) ≫
        K.homologyπ k :=
  rfl

include hH in
/-- **The inclusion of the local truncation is a quasi-isomorphism.** Over each member `V m`
of the cover it is the inclusion of the good truncation in degrees `≤ ℓ m`, and the cohomology
of `K` over `V m` is concentrated in degree `ℓ m`. -/
theorem quasiIso_truncInclusion : QuasiIso (truncInclusion K hV hX) := by
  refine quasiIso_of_coversTop (coversTop hV) _ fun m => ?_
  let F := _root_.SheafOfModules.overFunctor R (V m)
  let := LocalCokernel.overFunctor_preservesFiniteLimits (R := R) (V m)
  let := preservesHomology_overFunctor (R := R) (V m)
  have hF : ∀ (a : ℤ) (P : ℤ → Prop) [DecidablePred P],
      F.map (proj K hV hX a P) = if P (ℓ m) then 𝟙 _ else 0 :=
    fun a P _ => overFunctor_map_proj K hV hX a P m
  have hA : ∀ k, k ≤ ℓ m → IsIso (F.map (kernel.ι (proj K hV hX k (· < k)))) := fun k hk =>
    KernelFork.IsLimit.isIso_ι _ (KernelFork.mapIsLimit _ (kernelIsKernel _) F)
      (by rw [hF, ite_eq_right (by omega)])
  have hiso : ∀ k, k < ℓ m → IsIso (F.map (truncι K hV hX k)) := fun k hk => by
    have := hA k hk.le
    have : IsIso (F.map (kernel.ι (kernel.ι (proj K hV hX k (· < k)) ≫ K.d k (k + 1) ≫
        proj K hV hX (k + 1) (· = k)))) :=
      KernelFork.IsLimit.isIso_ι _ (KernelFork.mapIsLimit _ (kernelIsKernel _) F)
        (by rw [F.map_comp, F.map_comp, hF, ite_eq_right (by omega), comp_zero, comp_zero])
    rw [truncι, F.map_comp]
    infer_instance
  have hzero : ∀ k, ℓ m < k → IsZero (F.obj (truncX K hV hX k)) := fun k hk => by
    have h0 : F.map (kernel.ι (proj K hV hX k (· < k))) = 0 := by
      have h := F.congr_map (kernel.condition (proj K hV hX k (· < k)))
      rwa [F.map_comp, hF, ite_eq_left hk, Category.comp_id, F.map_zero] at h
    exact IsZero.of_mono_eq_zero (F.map (truncι K hV hX k))
      (by rw [truncι, F.map_comp, h0, comp_zero])
  have hKex : ∀ k, k ≠ ℓ m → ((F.mapHomologicalComplex _).obj K).ExactAt k := fun k hk => by
    rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
    exact IsZero.of_iso (hH m k hk) ((K.sc k).mapHomologyIso F)
  rw [quasiIso_iff]
  intro k
  rcases lt_trichotomy k (ℓ m) with hk | hk | hk
  · rw [quasiIsoAt_iff_exactAt' _ k (hKex k hk.ne),
      HomologicalComplex.exactAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp)]
    let φ := (HomologicalComplex.shortComplexFunctor' _ _ (k - 1) k (k + 1)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (truncInclusion K hV hX))
    have : IsIso φ.τ₁ := hiso (k - 1) (by omega)
    have : IsIso φ.τ₂ := hiso k hk
    have : Mono φ.τ₃ := F.map_mono (truncι K hV hX (k + 1))
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ,
      ← HomologicalComplex.exactAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp)]
    exact hKex k hk.ne
  · rw [quasiIsoAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp), ShortComplex.quasiIso_iff]
    exact isIso_homologyMap_of_isLimit_τ₂ _
      (@IsIso.epi_of_iso _ _ _ _ _ (hiso (k - 1) (by omega)))
      ((hzero (k + 1) (by omega)).eq_of_tgt _ _) (isLimitOverFunctorMapTruncι K hV hX m k hk)
  · rw [quasiIsoAt_iff_exactAt' _ k (hKex k hk.ne')]
    exact HomologicalComplex.ExactAt.of_isZero (hzero k hk)

include hH in
/-- **The projection of the local truncation onto the cohomology is a quasi-isomorphism.** In
each degree its homology map is the homology map of `truncInclusion` followed by the canonical
identification of the cohomology of a complex with zero differential with its terms; the two
differ by the part of the truncation living over members of degree `> k`, whose class in the
`k`-th cohomology of `K` vanishes locally, hence globally. -/
theorem quasiIso_truncProj : QuasiIso (truncProj K hV hX) := by
  have hι := quasiIso_truncInclusion K hV hX hH
  refine quasiIso_of_iCycles_comp_eq (truncInclusion K hV hX) (truncProj K hV hX)
    (fun i j => rfl) (fun k => Iso.refl (K.homology k)) fun k => ?_
  refine hom_ext_of_coversTop (coversTop hV) fun m => ?_
  let F := _root_.SheafOfModules.overFunctor R (V m)
  let := LocalCokernel.overFunctor_preservesFiniteLimits (R := R) (V m)
  by_cases hkm : k < ℓ m
  · exact (hH m k hkm.ne).eq_of_tgt _ _
  · have he : F.map (proj K hV hX k (· ≤ k)) = 𝟙 _ := by
      rw [overFunctor_map_proj, ite_eq_left (by omega)]
    change F.map ((trunc K hV hX).iCycles k ≫ K.liftCycles ((truncInclusion K hV hX).f k ≫
      proj K hV hX k (· ≤ k)) (k + 1) (by simp) (truncInclusion_f_proj_le_d K hV hX k) ≫
        K.homologyπ k) =
      F.map (HomologicalComplex.cyclesMap (truncInclusion K hV hX) k ≫ K.homologyπ k ≫
        𝟙 (K.homology k))
    rw [Category.comp_id, ← Category.assoc, F.map_comp, F.map_comp _ (K.homologyπ k)]
    congr 1
    rw [← cancel_mono (F.map (K.iCycles k)), ← F.map_comp, ← F.map_comp, Category.assoc,
      HomologicalComplex.liftCycles_i, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      F.map_comp _ (proj K hV hX k (· ≤ k)), he, Category.comp_id]

end LocallyConcentrated

end Formality

end Space

/-- **Formality of a complex whose cohomology is locally concentrated in one degree.** Let `K`
be a complex of sheaves of `R`-modules on a topological space `X`, let `V` be an open covering
of `X` and `ℓ` a degree attached to each of its members. Assume that over each `V i` the
cohomology sheaves of `K` vanish outside degree `ℓ i`, and that the terms of `K` vanish over
`V i ⊓ V j` whenever `ℓ i ≠ ℓ j`. Then `K` is isomorphic, in the derived category, to the complex
of its cohomology sheaves with zero differential.

The derived category is an arbitrary model `[HasDerivedCategory.{w} (SheafOfModules R)]`: the
isomorphism is a roof of two quasi-isomorphisms of complexes, which become invertible at any
model. -/
theorem nonempty_iso_zeroDifferentialComplex_homology_of_cover {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ W : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u}]
    [∀ W : Opens X,
      ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) {ι : Type*} (V : ι → Opens X)
    (hV : (⨆ i, V i) = ⊤) (ℓ : ι → ℤ)
    (hH : ∀ i k, k ≠ ℓ i → IsZero ((SheafOfModules.overFunctor R (V i)).obj (K.homology k)))
    (hX : ∀ i j k, ℓ i ≠ ℓ j →
      IsZero ((SheafOfModules.overFunctor R (V i ⊓ V j)).obj (K.X k))) :
    Nonempty (DerivedCategory.Q.obj K ≅
      DerivedCategory.Q.obj (CochainComplex.zeroDifferentialComplex fun k => K.homology k)) := by
  have : IsIso (DerivedCategory.Q.map (LocallyConcentrated.truncInclusion K hV hX)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (LocallyConcentrated.quasiIso_truncInclusion K hV hX hH)
  have : IsIso (DerivedCategory.Q.map (LocallyConcentrated.truncProj K hV hX)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
      (LocallyConcentrated.quasiIso_truncProj K hV hX hH)
  exact ⟨(asIso (DerivedCategory.Q.map (LocallyConcentrated.truncInclusion K hV hX))).symm ≪≫
    asIso (DerivedCategory.Q.map (LocallyConcentrated.truncProj K hV hX))⟩

end Stacks.SheafOfModules
