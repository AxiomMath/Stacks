module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensor
public import StacksFrontier.Homology.KFlat.Flat
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Lemma 21.17.9 / Tag 06YR.

Let `(C, O)` be a ringed site: a site `C` (a category with a Grothendieck
topology `J`) together with a sheaf of (commutative, unital) rings `O` on `C`.
Write `Mod(O)` for the abelian category of sheaves of `O`-modules on `C`.

The lemma states: if `K_1 -> K_2 -> K_3 -> ...` is a system of K-flat complexes
of `O`-modules (indexed by the positive integers, a filtered poset), then the
termwise colimit `colim_i K_i` is again a K-flat complex of `O`-modules.

The proof rests on two facts:
* `Tot(F ⊗_O -)` commutes with termwise filtered colimits, and
* filtered colimits are exact in the abelian category `Mod(O)`,
so the colimit of the (acyclic, by K-flatness) complexes `Tot(F ⊗_O K_i)` is
acyclic, hence `colim_i K_i` is K-flat.
-/

/-
## Modelling notes

* The category `Mod(O)` of sheaves of `O`-modules on a ringed site is modelled by
  `SheafOfModules.{v} R`, where `R : Sheaf J RingCat` is the sheaf of rings `O` on
  the site `(C, J)`.  This is an abelian category.

* All complexes are cochain complexes of `O`-modules with differential of degree
  `+1`, i.e. objects of `CochainComplex (Mod(O)) ℤ` (here `ComplexShape.up ℤ`).

* Definition 1 (tensor product of `O`-modules).  The tensor product
  `F ⊗_O G` is the sheafification of the presheaf `U ↦ F(U) ⊗_{O(U)} G(U)`.  It is
  a right exact additive bifunctor commuting with arbitrary colimits in each
  variable.  This is `Stacks.SheafOfModules.Tensor.sheafTensor`, the bifunctor the
  main theorem is stated for.  The supporting lemmas are proved for an arbitrary
  bifunctor `F : Mod(O) ⥤ Mod(O) ⥤ Mod(O)` additive in each variable, carrying the
  colimit-preservation property of Definition 1 as a hypothesis `hF₁`; for
  `F = ⊗_O` that hypothesis is discharged by
  `SheafOfModules.preservesColimitsOfSize_sheafTensor_obj`, which is the statement
  that `ℱ ⊗_O -` is a left adjoint, `Mod(O)` being monoidal closed.

* Definition 2 (total complex of the tensor of two complexes).  Given a bifunctor
  `F` as above, `Functor.mapBifunctorHomologicalComplex` produces the double
  complex `p, q ↦ F(F^p, G^q)`, and `HomologicalComplex₂.total` forms its
  direct-sum total complex.  The total complex shape instance
  `TotalComplexShape (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)`
  is precisely the Koszul sign rule `d(x ⊗ y) = d_F x ⊗ y + (-1)^p x ⊗ d_G y`.

* Definition 3 (acyclic complex).  `H^n(X) = 0` for all `n`, with cohomology taken
  in `Mod(O)`; `IsZero (X.homology n)`.

* Definition 5 (system and termwise colimit).  A system indexed by the positive
  integers is a functor `ℕ ⥤ CochainComplex (Mod(O)) ℤ` (the poset `(ℕ, ≤)` is
  filtered, equivalent to `ℤ_{≥1}`).  Its colimit in `CochainComplex (Mod(O)) ℤ`
  is automatically computed termwise, because the evaluation functor
  `HomologicalComplex.eval` preserves colimits (recorded as the correctness
  theorem `systemColimit_termwise`).

The supporting lemmas are stated over a sheaf of rings `R` carrying the instances
`Abelian (Mod(O))`, `CategoryWithHomology (Mod(O))` and `HasColimits (Mod(O))`.  For the
sheaf of rings underlying a sheaf of commutative rings — the case of the main theorem —
all three are instances: the first two come from `SheafOfModules.instAbelian` and the
third from `Mathlib/Algebra/Category/ModuleCat/Sheaf/Colimits.lean`.
-/

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- `Mod(O)`: the category of sheaves of `O`-modules on the ringed site `(C, O)`,
where `R` plays the role of the sheaf of rings `O`. -/
@[ega "0 4.1.3" "more general",
  sga "4 II 6.3.2",
  sga "4 II 6.3.3" "more general",
  sga "4 II 6.7",
  sga "4 IV 11.1.2",
  sga "4 V 3.5",
  sga "4 V 6.13",
  sga "4 Vbis 2.4.0" "partial",
  sga "4 Vbis 4.1.0" "fiber G_X = Mod(Z_X)",
  sga "4 Vbis 4.3.0" "fiber category F_{n_X}",
  sga "4 XVII 7.0.1" "more general",
  sga "5 I App.1.1",
  sga "6 I 4.8" "ambient S-category C",
  sga "6 II 2.0",
  sga "6 II 2.3.2",
  sga "6 III 5.1",
  sga "7 IX 9.4",
  sga "7 VI 3.1(a)" "more general"]
abbrev ModO (R : Sheaf J RingCat.{w}) := SheafOfModules.{w} R

variable (R : Sheaf J RingCat.{w})
variable [Abelian (ModO R)] [CategoryWithHomology (ModO R)] [HasColimits (ModO R)]

/-- The cochain complex shape: differentials of degree `+1`, indexed by `ℤ`. -/
@[ega "0 11.2.1" "partial", sga "6 I 1.1.5"]
abbrev shapeℤ : ComplexShape ℤ := ComplexShape.up ℤ

-- Main Definition(s)

/--
**Definition 2 (Total complex of the tensor product of two complexes).**

Given a bifunctor `F : Mod(O) ⥤ Mod(O) ⥤ Mod(O)` representing the tensor product
`- ⊗_O -` (Definition 1), and two cochain complexes `X`, `Y` of `O`-modules,
`totTensor R F X Y = Tot(X ⊗_O Y)` is the direct-sum total complex of the double
complex `p, q ↦ F(X^p, Y^q)`.  Its differential is governed by the Koszul sign
rule via the canonical `TotalComplexShape` on `ℤ`.
-/
@[sga "4 XVII 1.1.10" "more general", sga "7 VII 3.6" "more general"]
noncomputable def totTensor (F : ModO R ⥤ ModO R ⥤ ModO R)
    [F.Additive] [∀ X, (F.obj X).Additive]
    (X Y : CochainComplex (ModO R) ℤ) : CochainComplex (ModO R) ℤ :=
  (((F.mapBifunctorHomologicalComplex shapeℤ shapeℤ).obj X).obj Y).total shapeℤ

/-!
**Definition 3 (Acyclic complex).**

A cochain complex `X` of `O`-modules is acyclic if all its cohomology sheaves vanish:
`H^n(X) = 0` for every `n ∈ ℤ`.  This is `CategoryTheory.HomologicalComplex.Acyclic`, which is
`∀ i, K.ExactAt i`; `CategoryTheory.HomologicalComplex.exactAt_iff_isZero_homology` identifies
exactness at `i` with the vanishing of the `i`-th homology.
-/

/--
**Definition 4 (K-flat complex; Stacks Tag 06YN).**

A cochain complex `K` of `O`-modules is K-flat (with respect to the tensor
product `F = - ⊗_O -`) if for every acyclic complex `X` of `O`-modules, the total
complex `Tot(X ⊗_O K)` is acyclic.
-/
def IsKFlat (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (K : CochainComplex (ModO R) ℤ) : Prop :=
  ∀ X : CochainComplex (ModO R) ℤ, X.Acyclic → (totTensor R F X K).Acyclic

/--
**Definition 5 (System and termwise colimit of complexes).**

A *system of complexes* `K_1 → K_2 → …` indexed by the positive integers is a
functor from the filtered poset `(ℕ, ≤)` to cochain complexes of `O`-modules.
(Working with `ℕ` rather than `ℤ_{≥1}` is harmless: both are filtered posets order
isomorphic to one another; only filteredness is used.)
-/
abbrev SystemOfComplexes (R : Sheaf J RingCat.{w}) := ℕ ⥤ CochainComplex (ModO R) ℤ

/-- The (termwise) colimit `colim_i K_i` of a system of complexes. -/
noncomputable def systemColimit (D : SystemOfComplexes R) : CochainComplex (ModO R) ℤ :=
  colimit D

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/--
**Correctness of Definition 5 (termwise colimit).**

The colimit `colim_i K_i` of a system of complexes is computed termwise: for each
degree `n`, the `n`-th term `(colim_i K_i)^n` is the colimit of the `n`-th terms
`colim_i K_i^n`.  Equivalently, the evaluation functor
`HomologicalComplex.eval (Mod(O)) shapeℤ n`, which sends a complex to its `n`-th
term, preserves the colimit of `D`.  This is the content of the slogan that the
colimit is "taken termwise".
-/
theorem systemColimit_termwise (D : SystemOfComplexes R) (n : ℤ) :
    PreservesColimit D (HomologicalComplex.eval (ModO R) shapeℤ n) := by
  -- The evaluation functor on homological complexes preserves all colimits (it is a
  -- component of the equality `colim` is computed degreewise); Mathlib provides the
  -- instance `HomologicalComplex.eval ... preservesColimit`.
  infer_instance

-- Supporting lemmas for the proof of Statement 1.

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- If `G : Mod(O) ⥤ Mod(O)` preserves filtered colimits of shape `ℕ`, then the
induced functor on cochain complexes `G.mapHomologicalComplex shapeℤ` also
preserves them.  This is checked degreewise via `HomologicalComplex.isColimitOfEval`,
using the definitional identity
`G.mapHomologicalComplex shapeℤ ⋙ eval q = eval q ⋙ G`. -/
theorem preservesColimitsOfShape_mapHomologicalComplex
    (G : ModO R ⥤ ModO R) [G.PreservesZeroMorphisms]
    [PreservesColimitsOfShape ℕ G] :
    PreservesColimitsOfShape ℕ (G.mapHomologicalComplex shapeℤ) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun q =>
    (inferInstance : PreservesColimitsOfShape ℕ (HomologicalComplex.eval _ shapeℤ q ⋙ G))

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- `Tot(X ⊗_O -)` before totalisation, i.e. the double-complex-valued functor
`(F.mapBifunctorHomologicalComplex …).obj X`, preserves filtered colimits of
shape `ℕ`.  This is checked degreewise (via `HomologicalComplex.isColimitOfEval`):
at homological degree `p` it agrees definitionally with
`(F.obj (X.X p)).mapHomologicalComplex shapeℤ`, which preserves colimits of shape
`ℕ` by `preservesColimitsOfShape_mapHomologicalComplex` together with the
hypothesis `hF₁ (X.X p)`. -/
theorem preservesColimitsOfShape_mapBifunctorObj
    (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (hF₁ : ∀ A : ModO R, PreservesColimitsOfShape ℕ (F.obj A))
    (X : CochainComplex (ModO R) ℤ) :
    PreservesColimitsOfShape ℕ ((F.mapBifunctorHomologicalComplex shapeℤ shapeℤ).obj X) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun p => by
    have : PreservesColimitsOfShape ℕ (F.obj (X.X p)) := hF₁ (X.X p)
    have := preservesColimitsOfShape_mapHomologicalComplex R (F.obj (X.X p))
    exact (inferInstance : PreservesColimitsOfShape ℕ
      ((F.obj (X.X p)).mapHomologicalComplex shapeℤ))

/- The total-complex functor `Tot : HomologicalComplex₂ … ⥤ CochainComplex …`
preserves filtered colimits of shape `ℕ`.  [Background note for the two
declarations below; see their own docstrings for the live formalisation plan.]

**Mathematical argument (the one genuinely total-complex-specific step of Tag 06YR).**
In each total degree `n` the object `Tot(K)^n = ⊕_{p+q=n} K^{p,q}` is a coproduct
(this is the *direct sum* total complex, Stacks Tag 06YL / Definition 2; in
Mathlib it is `HomologicalComplex₂.total`, whose `n`-th term is the coproduct
`∐_{(p,q), p+q=n} K.X p |>.X q` over the index set `(ComplexShape.up ℤ).TotalComplexShape …`).
Colimits commute with colimits; in particular coproducts commute with the filtered
`ℕ`-colimit.  Therefore, evaluating at total degree `n`,
  `Tot(colim_i K_i)^n = ⊕_{p+q=n} (colim_i K_i)^{p,q}`
                      `= ⊕_{p+q=n} colim_i K_i^{p,q}`   (colimits are computed degreewise in
                      `HomologicalComplex₂`)
                      `= colim_i ⊕_{p+q=n} K_i^{p,q}`    (coproduct ⊗ filtered colimit interchange)
                      `= colim_i Tot(K_i)^n`.
Since this holds in every total degree and is compatible with the differentials,
`HomologicalComplex.isColimitOfEval` upgrades these degreewise isomorphisms to an
isomorphism of complexes, exhibiting `Tot` as preserving the colimit.

**Formalisation strategy.**  Use `preservesColimit_of_preserves_colimit_cocone`
with `colimit.isColimit`, reduce to a degreewise statement via
`HomologicalComplex.isColimitOfEval`, then in each total degree `n` identify
`(totalFunctor … ⋙ eval n)` with the coproduct functor
`∐_{(p,q) ∈ (shapeℤ).antidiagonal-of-totalComplexShape n} (eval p ⋙ eval q)` and
invoke that coproducts preserve colimits (`Limits.preservesColimitsOfShape` of a
`colim`/coproduct functor, e.g. via `HomologicalComplex₂.total` API and the fact
that `D.X p |>.X q` evaluation functors preserve `ℕ`-colimits, combined with
`preservesColimit_of_preserves_coproduct`-style interchange).  This requires
unfolding the `HomologicalComplex₂.total` definition and using its `D.HasTotal`
coproduct structure (`HomologicalComplex₂.totalAux`/`ιTotal`/`isColimitCofan`-type
API).  Not yet packaged in Mathlib for `HomologicalComplex₂.totalFunctor`; this is
THE hard subgoal of the decomposition. -/

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- **Per–total–degree colimit preservation (the hard core of Tag 06YR).**

For every total degree `n`, the functor sending a double complex `K` to the
`n`-th term of its total complex,
`HomologicalComplex₂.totalFunctor … ⋙ HomologicalComplex.eval (ModO R) shapeℤ n`,
preserves the `ℕ`-colimit of `D'`.

**Why this is true (and how to prove it in Lean).**
By `HomologicalComplex₂.totalFunctor_obj` and the definition of `total`/`HasTotal`,
`(totalFunctor.obj K ⋙ eval n).obj K = (K.total shapeℤ).X n =
   K.toGradedObject.mapObj (shapeℤ.π shapeℤ shapeℤ) n`,
and `GradedObject.isColimitCofanMapObj` exhibits this object as the coproduct
`∐_{(p,q), π(p,q)=n} (K.X p).X q` via the cofan `GradedObject.cofanMapObj`,
i.e. the colimit of `Discrete.functor (K.toGradedObject.mapObjFun π n)`.

So `totalFunctor ⋙ eval n` is (naturally) the coproduct over the fixed antidiagonal
index `{(p,q) : π(p,q)=n}` of the bidegree-evaluation functors
`ev_{p,q} : K ↦ (K.X p).X q`.  Now:
* each `ev_{p,q}` preserves the `ℕ`-colimit (`HomologicalComplex.eval` preserves all
  colimits — the instance already used in `systemColimit_termwise`); and
* the coproduct functor `∐ : (Discrete ι ⥤ ModO R) ⥤ ModO R`, being naturally
  isomorphic to `colim` over `Discrete ι`, is a **left adjoint** (`Limits.colimConstAdj`)
  and therefore preserves *all* colimits, in particular the `ℕ`-colimit.  (This is the
  "coproducts commute with filtered colimits" interchange; in Mathlib it is FREE from
  `colim` being a left adjoint — no finiteness of the index set is needed.)

Concretely the Lean proof should: package, for each `K`, the colimit cofan
`GradedObject.isColimitCofanMapObj K.toGradedObject π n`; show the comparison map of
the image cocone is an isomorphism using that `colim`/coproduct over `Discrete (fiber n)`
preserves the `ℕ`-colimit (`isColimitOfPreserves` of the coproduct functor), and that
the per-summand evaluation `ev_{p,q}` preserves it; then transport along
`GradedObject.cofanMapObj`/`ιMapObj` naturality; the
obstruction in the middle step is resolved by `colimConstAdj`. -/
theorem preservesColimit_totalFunctor_eval
    (D' : ℕ ⥤ HomologicalComplex₂ (ModO R) shapeℤ shapeℤ) (n : ℤ) :
    PreservesColimit D'
      (HomologicalComplex₂.totalFunctor (ModO R) shapeℤ shapeℤ shapeℤ ⋙
        HomologicalComplex.eval (ModO R) shapeℤ n) := by
  -- The fiber of the antidiagonal: index set of the coproduct in total degree `n`.
  let π : ℤ × ℤ → ℤ := (shapeℤ).π shapeℤ shapeℤ
  -- The family of bidegree-evaluation functors, indexed by the fiber `π ⁻¹' {n}`.
  let ev : (↑(π ⁻¹' {n})) → (HomologicalComplex₂ (ModO R) shapeℤ shapeℤ ⥤ ModO R) :=
    fun i => HomologicalComplex.eval (HomologicalComplex (ModO R) shapeℤ) shapeℤ i.1.1 ⋙
      HomologicalComplex.eval (ModO R) shapeℤ i.1.2
  -- Package them as a functor `B_n : HC₂ ⥤ (Discrete fiber ⥤ ModO R)`.
  let B : HomologicalComplex₂ (ModO R) shapeℤ shapeℤ ⥤
      (Discrete (↑(π ⁻¹' {n})) ⥤ ModO R) := (Discrete.functor ev).flip
  -- `B ⋙ colim` is naturally isomorphic to `totalFunctor ⋙ eval n`.
  have iso : (B ⋙ colim) ≅ (HomologicalComplex₂.totalFunctor (ModO R) shapeℤ shapeℤ shapeℤ ⋙
        HomologicalComplex.eval (ModO R) shapeℤ n) := by
    refine NatIso.ofComponents (fun K => ?_) ?_
    · refine (HasColimit.isoOfNatIso (F := B.obj K)
        (G := Discrete.functor (K.toGradedObject.mapObjFun π n))
        (Discrete.natIso (fun _ => Iso.refl _))).trans
        (colimit.isoColimitCocone ⟨_, K.toGradedObject.isColimitCofanMapObj π n⟩)
    intro K L f
    apply Limits.colimit.hom_ext
    intro j
    obtain ⟨⟨pq, hpq⟩⟩ := j
    have hBmap : (B.map f).app ⟨⟨pq, hpq⟩⟩ = (f.f pq.1).f pq.2 := rfl
    simp only [Functor.comp_map, Iso.trans_hom, colim_map,
      Category.assoc, ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
      colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc,
      Discrete.natIso_hom_app, Iso.refl_hom, Category.id_comp, hBmap]
    show (f.f pq.1).f pq.2 ≫ L.toGradedObject.ιMapObj π pq n hpq
      = K.toGradedObject.ιMapObj π pq n hpq ≫ (HomologicalComplex₂.total.map f shapeℤ).f n
    exact (K.ιTotal_map L f shapeℤ pq.1 pq.2 n hpq).symm
  -- `B` preserves the colimit (it is built pointwise from evaluation functors, each of
  -- which preserves all colimits), and `colim` preserves all colimits (left adjoint).
  have : PreservesColimit D' B := by
    refine preservesColimit_of_evaluation _ _ (fun k => ?_)
    have : B ⋙ (evaluation (Discrete (↑(π ⁻¹' {n}))) (ModO R)).obj k = ev k.as := rfl
    rw [this]
    exact comp_preservesColimit _ _
  have : PreservesColimit (D' ⋙ B) (colim (J := Discrete (↑(π ⁻¹' {n}))) (C := ModO R)) :=
    inferInstance
  have : PreservesColimit D' (B ⋙ colim) := comp_preservesColimit _ _
  exact preservesColimit_of_natIso _ iso

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- The total-complex functor on double complexes of `O`-modules, indexed by `ℤ × ℤ`,
preserves colimits of shape `ℕ`. -/
theorem preservesColimitsOfShape_totalFunctor :
    PreservesColimitsOfShape ℕ
      (HomologicalComplex₂.totalFunctor (ModO R) shapeℤ shapeℤ shapeℤ) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n =>
    ⟨fun {D'} => preservesColimit_totalFunctor_eval R D' n⟩

/-- The endofunctor `Tot(X ⊗_O -) : CochainComplex(Mod O) ⥤ CochainComplex(Mod O)`
on cochain complexes, i.e. `Y ↦ totTensor R F X Y`. -/
@[sga "4 XVII 7.3.3" "special case"]
noncomputable def totTensorFunctor
    (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (X : CochainComplex (ModO R) ℤ) :
    CochainComplex (ModO R) ℤ ⥤ CochainComplex (ModO R) ℤ :=
  ((F.mapBifunctorHomologicalComplex shapeℤ shapeℤ).obj X) ⋙
    HomologicalComplex₂.totalFunctor (ModO R) shapeℤ shapeℤ shapeℤ

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- The functor `totTensorFunctor R F X` sends `Y` to `totTensor R F X Y`. -/
@[simp] lemma totTensorFunctor_obj
    (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (X Y : CochainComplex (ModO R) ℤ) :
    (totTensorFunctor R F X).obj Y = totTensor R F X Y := rfl

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/-- `Tot(X ⊗_O -)` preserves filtered colimits of shape `ℕ`: it is the composite
of `(F.mapBifunctorHomologicalComplex …).obj X` (which preserves them by
`preservesColimitsOfShape_mapBifunctorObj`) and the total-complex functor (which
preserves them by `preservesColimitsOfShape_totalFunctor`). -/
theorem preservesColimitsOfShape_totTensorFunctor
    (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (hF₁ : ∀ A : ModO R, PreservesColimitsOfShape ℕ (F.obj A))
    (X : CochainComplex (ModO R) ℤ) :
    PreservesColimitsOfShape ℕ (totTensorFunctor R F X) := by
  have := preservesColimitsOfShape_mapBifunctorObj R F hF₁ X
  have := preservesColimitsOfShape_totalFunctor R
  unfold totTensorFunctor
  exact comp_preservesColimitsOfShape _ _

-- Main Statement(s)

omit [Abelian (ModO R)] [CategoryWithHomology (ModO R)] in
/--
**Statement 1 for an abstract tensor product.**

Let `D : K_1 → K_2 → K_3 → …` be a system of complexes of `O`-modules, K-flat for a
bifunctor `F : Mod(O) ⥤ Mod(O) ⥤ Mod(O)` additive in each variable.  Then the termwise
colimit `colim_i K_i` is K-flat for `F`, provided

* `hF₁` : `F` preserves colimits of shape `ℕ` in its second variable, so that
  `Tot(X ⊗_O -)` commutes with the termwise filtered colimit; and
* `hcolim_exact` : a colimit over `ℕ` of acyclic complexes of `O`-modules is acyclic.

Both hold for `F = ⊗_O` and are discharged there; see
`colim_of_system_KFlat_isKFlat`, which is the lemma of Tag 06YR.
-/
theorem colim_of_system_KFlat_isKFlat_of_bifunctor
    (F : ModO R ⥤ ModO R ⥤ ModO R) [F.Additive] [∀ X, (F.obj X).Additive]
    (hF₁ : ∀ X : ModO R, PreservesColimitsOfShape ℕ (F.obj X))
    (hcolim_exact :
      ∀ (E : ℕ ⥤ CochainComplex (ModO R) ℤ),
        (∀ i, (E.obj i).Acyclic) → (colimit E).Acyclic)
    (D : SystemOfComplexes R) (hD : ∀ i, IsKFlat R F (D.obj i)) :
    IsKFlat R F (systemColimit R D) := by
  -- Unfold K-flatness: fix an acyclic `X`; show `Tot(X ⊗_O colim_i K_i)` is acyclic.
  intro X hX
  -- The system of total complexes `i ↦ Tot(X ⊗_O K_i)`.
  set E : ℕ ⥤ CochainComplex (ModO R) ℤ := D ⋙ totTensorFunctor R F X with hE
  -- Each `Tot(X ⊗_O K_i)` is acyclic, since `K_i` is K-flat and `X` acyclic.
  have hEacyc : ∀ i, (E.obj i).Acyclic := by
    intro i
    have := hD i X hX
    simpa [hE, totTensorFunctor_obj] using this
  -- Hence the filtered colimit `colim_i Tot(X ⊗_O K_i)` is acyclic (exactness of
  -- filtered colimits in `Mod(O)`).
  have hcolimE : (colimit E).Acyclic := hcolim_exact E hEacyc
  -- `Tot(X ⊗_O -)` commutes with the termwise filtered colimit, giving
  -- `Tot(X ⊗_O colim_i K_i) ≅ colim_i Tot(X ⊗_O K_i)`.
  have := preservesColimitsOfShape_totTensorFunctor R F hF₁ X
  have : PreservesColimit D (totTensorFunctor R F X) := inferInstance
  have e : (totTensorFunctor R F X).obj (colimit D) ≅ colimit E :=
    (preservesColimitIso (totTensorFunctor R F X) D).trans
      (HasColimit.isoOfNatIso (Iso.refl _))
  -- Transport acyclicity along this isomorphism.
  rw [show totTensor R F X (systemColimit R D)
        = (totTensorFunctor R F X).obj (colimit D) from rfl]
  exact fun i => (hcolimE i).of_iso e.symm

section SheafTensor

open Stacks.SheafOfModules.Tensor

variable (O : Sheaf J CommRingCat.{max u v}) [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/--
**Statement 1 (Stacks Lemma 21.17.9 / Tag 06YR).**

Let `(C, O)` be a ringed site and let `D : K_1 → K_2 → K_3 → …` be a system of complexes
of `O`-modules which are K-flat for the tensor product `⊗_O` of Definition 1.  Then the
termwise colimit `colim_i K_i` is K-flat.

The two structural facts of the proof are the two hypotheses of
`colim_of_system_KFlat_isKFlat_of_bifunctor`, and both are theorems here: `⊗_O` commutes
with colimits in each variable because `Mod(O)` is monoidal closed, so `ℱ ⊗_O -` is a left
adjoint (`SheafOfModules.preservesColimitsOfSize_sheafTensor_obj`); and colimits over `ℕ`
are exact in `Mod(O)` by AB5
(`SheafOfModules.DifferentialGradedModule.hasExactColimitsOfShape_nat`), so a colimit of
acyclic complexes is acyclic (`CochainComplex.KFlat.acyclic_colimit`).
-/
@[stacks 06YR]
theorem colim_of_system_KFlat_isKFlat (D : SystemOfComplexes (ringSheaf O))
    (hD : ∀ i, IsKFlat (ringSheaf O) (sheafTensor O) (D.obj i)) :
    IsKFlat (ringSheaf O) (sheafTensor O) (systemColimit (ringSheaf O) D) :=
  have := SheafOfModules.DifferentialGradedModule.hasExactColimitsOfShape_nat (ringSheaf O)
  colim_of_system_KFlat_isKFlat_of_bifunctor (ringSheaf O) (sheafTensor O)
    (fun _ => ⟨fun {_} => inferInstance⟩)
    (fun E hE => CochainComplex.KFlat.acyclic_colimit E hE) D hD

end SheafTensor
