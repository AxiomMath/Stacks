module

public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.DiagonalTensorHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexComposition
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal morphism `Tot(K ⊗ SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗ L))`

Let `(X, O_X)` be a ringed space and let `K`, `L` and `M` be complexes of `O_X`-modules. There
is a canonical morphism of complexes of `O_X`-modules
`Tot(K ⊗_{O_X} SheafHom^•(M, L)) ⟶ SheafHom^•(M, Tot(K ⊗_{O_X} L))`, functorial in all three
complexes.

The total tensor product is sheafified degreewise, so a general section of its source is only
locally a sum of homogeneous pure tensors; the morphism is therefore pinned down by its effect
on those, namely `k ⊗ φ ↦ (m ↦ k ⊗ φ(m))`, with no sign. `DiagonalBetterConstruction` records
a morphism together with that characterisation, which is what makes the three functoriality
statements below say something: a morphism with no constraint on its values is satisfied by
the zero morphism.

The morphism is the composite of the diagonal morphism `K ⟶ SheafHom^•(L, Tot(K ⊗ L))` of
[Stacks, Tag 0A8Q] with the composition morphism of internal Hom complexes of
[Stacks, Tag 0A91]; both are unsigned on homogeneous local pure tensors, and their composite
is the unsigned map above, which is the sheaf-level reading of the algebraic morphism
`Stacks.HomComplex.TensorHomComparison.theta`.

## Main definitions

* `Stacks.SheafOfModules.DiagonalBetterConstruction`: diagonal morphisms, specified by their
  action on all homogeneous local pure tensors.
* `Stacks.SheafOfModules.diagonalBetterConstruction` (Stacks 0BYR): the canonical such
  morphism.
* `Stacks.SheafOfModules.diagonalBetter`: the canonical diagonal morphism attached to three
  complexes.

## Main results

* `Stacks.SheafOfModules.tensorTotal_hom_ext`: two morphisms out of a total tensor product
  that agree on all homogeneous local pure tensors are equal.
* `Stacks.SheafOfModules.tensorTotalSection_restrict`: homogeneous local pure tensors are
  compatible with restriction to a smaller open set.
* `Stacks.SheafOfModules.DiagonalBetterConstruction.diagonal_unique`: the action on
  homogeneous local pure tensors determines the diagonal morphism.
* `Stacks.SheafOfModules.diagonalBetter_natural_left`,
  `Stacks.SheafOfModules.diagonalBetter_natural_right` and
  `Stacks.SheafOfModules.diagonalBetter_natural_hom` (Stacks 0BYR): the diagonal morphism is
  covariant in the tensor factor, covariant in the target of the internal Hom, and
  contravariant in its source.

## Implementation notes

A morphism out of the degreewise sheafification `tensorTotal` is determined by its restriction
along the sheafification unit, and that restriction is determined on each summand of the
unsheafified total complex by its values on pure tensors; `tensorTotal_hom_ext` is that
statement, and `DiagonalBetterConstruction.hom_ext` combines it with the corresponding
extensionality for local sections of an internal Hom complex. All three functoriality
statements are then verified on homogeneous local pure tensors alone.

The degree of the value is carried as a variable constrained by an equation, so that the two
spellings `b + p` and `p + b` of a total degree never have to be identified by transport:
`homComplexComposition_tmul` restates the characterisation of the composition morphism at
an arbitrary such degree by substituting the equation.

A ringed space is a ringed site, so the composition morphism of
`Stacks.Cohomology.compositionConstruction` is used along `Stacks.SheafOfModules.ringedSite`
with no comparison layer, exactly as `Stacks.SheafOfModules.evaluationConstruction` uses the
evaluation morphism of a ringed site.

## References

* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYM](https://stacks.math.columbia.edu/tag/0BYM)
* [Stacks Project, Tag 0A8Q](https://stacks.math.columbia.edu/tag/0A8Q)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open CochainComplex.HomComplex

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- The unsheafified total complex of the tensor-product double complex of the underlying
presheaves of modules. -/
private noncomputable abbrev presheafTensorTotal
    (A B : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (PresheafOfModules.{u} (structureSheaf Rc).obj) ℤ :=
  HomologicalComplex.mapBifunctor (underlyingComplex Rc A) (underlyingComplex Rc B)
    (curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)) (ComplexShape.up ℤ)

/-- The identity morphism of complexes acts as the identity on local sections. -/
private lemma id_f_val_app (A : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ)
    (U : Opens X) (x : (A.X n).val.obj (op U)) :
    ((𝟙 A : A ⟶ A).f n).val.app (op U) x = x := rfl

/-- A composite of morphisms of complexes acts on local sections by composition. -/
private lemma comp_f_val_app {A B C : CochainComplex (StructureSheafModules Rc) ℤ}
    (u : A ⟶ B) (v : B ⟶ C) (n : ℤ) (U : Opens X) (z : (A.X n).val.obj (op U)) :
    ((u ≫ v).f n).val.app (op U) z = (v.f n).val.app (op U) ((u.f n).val.app (op U) z) := rfl

/-- Two morphisms out of a total tensor product that agree on every homogeneous local pure
tensor are equal: a morphism out of a degreewise sheafification is determined by its
restriction along the sheafification unit, and that restriction is determined on each summand
of the unsheafified total complex by its values on pure tensors. -/
theorem tensorTotal_hom_ext
    {A B T : CochainComplex (StructureSheafModules Rc) ℤ}
    {f g : tensorTotal Rc A B ⟶ T}
    (h : ∀ (U : Opens X) (t r : ℤ) (x : (A.X t).val.obj (op U))
        (y : (B.X r).val.obj (op U)),
      (f.f (t + r)).val.app (op U) (tensorTotalSection Rc A B U t r x y) =
        (g.f (t + r)).val.app (op U) (tensorTotalSection Rc A B U t r x y)) :
    f = g := by
  apply HomologicalComplex.hom_ext
  intro n
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheaf Rc).obj)).homEquiv
      ((presheafTensorTotal Rc A B).X n) (T.X n)).injective ?_
  show (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
      ((presheafTensorTotal Rc A B).X n) ≫ (f.f n).val =
    (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
      ((presheafTensorTotal Rc A B).X n) ≫ (g.f n).val
  refine HomologicalComplex.mapBifunctor.hom_ext fun t r hn => ?_
  obtain rfl : t + r = n := hn
  ext U : 1
  exact ModuleCat.MonoidalCategory.tensor_ext fun x y => h U.unop t r x y

/-- Homogeneous local pure tensors are compatible with restriction to a smaller open set. -/
theorem tensorTotalSection_restrict
    (A B : CochainComplex (StructureSheafModules Rc) ℤ) {U V : Opens X} (hVU : V ≤ U)
    (t r : ℤ) (x : (A.X t).val.obj (op U)) (y : (B.X r).val.obj (op U)) :
    ((tensorTotal Rc A B).X (t + r)).val.map (homOfLE hVU).op
        (tensorTotalSection Rc A B U t r x y) =
      tensorTotalSection Rc A B V t r ((A.X t).val.map (homOfLE hVU).op x)
        ((B.X r).val.map (homOfLE hVU).op y) := by
  let F := curriedTensor (PresheafOfModules.{u} (structureSheaf Rc).obj)
  let ι := HomologicalComplex.ιMapBifunctor (underlyingComplex Rc A) (underlyingComplex Rc B)
    F (ComplexShape.up ℤ) t r (t + r) rfl
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Rc).obj)).unit.app
    ((presheafTensorTotal Rc A B).X (t + r))
  have h1 : ((A.X t).val.map (homOfLE hVU).op x) ⊗ₜ[(structureSheaf Rc).obj.obj (op V)]
        ((B.X r).val.map (homOfLE hVU).op y) =
      (((F.obj ((underlyingComplex Rc A).X t)).obj ((underlyingComplex Rc B).X r)).map
        (homOfLE hVU).op) (x ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] y) :=
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (homOfLE hVU).op x y).symm
  have h2 := PresheafOfModules.naturality_apply ι (homOfLE hVU).op
    (x ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] y)
  have h3 := PresheafOfModules.naturality_apply η (homOfLE hVU).op
    (ι.app (op U) (x ⊗ₜ[(structureSheaf Rc).obj.obj (op U)] y))
  refine h3.symm.trans ?_
  refine (congrArg (fun z => η.app (op V) z) h2.symm).trans ?_
  exact (congrArg (fun z => η.app (op V) (ι.app (op V) z)) h1).symm

/-- Evaluating a local section of an internal Hom complex on a section over a smaller open set
is evaluating its restriction. -/
private lemma applyHomSection_restrict
    {K L : CochainComplex (StructureSheafModules Rc) ℤ} (H : SheafHomComplex Rc K L)
    {U V : Opens X} (hVU : V ≤ U) (n p q : ℤ) (hpq : p + n = q)
    (s : (H.obj.X n).val.obj (op U)) (x : (K.X p).val.obj (op V)) :
    ((AddCommGrpCat.Hom.hom ((H.sectionsIso U).hom.f n) s).v p q hpq).val.app
        (op (Over.mk (homOfLE hVU))) x =
      applyHomSection Rc H V n p q hpq ((H.obj.X n).val.map (homOfLE hVU).op s) x :=
  H.restrict_natural hVU n p q hpq s (le_refl V) x

/-- Two local sections of an internal Hom complex whose restrictions act in the same way on
every local section of the source are equal. -/
private lemma homSection_ext_restrict
    {K L : CochainComplex (StructureSheafModules Rc) ℤ} (H : SheafHomComplex Rc K L)
    (U : Opens X) (n : ℤ) {s t : (H.obj.X n).val.obj (op U)}
    (h : ∀ (p q : ℤ) (hpq : p + n = q) (V : Opens X) (hVU : V ≤ U)
      (x : (K.X p).val.obj (op V)),
      applyHomSection Rc H V n p q hpq ((H.obj.X n).val.map (homOfLE hVU).op s) x =
        applyHomSection Rc H V n p q hpq ((H.obj.X n).val.map (homOfLE hVU).op t) x) :
    s = t := by
  apply (AddCommGrpCat.mono_iff_injective ((H.sectionsIso U).hom.f n)).mp inferInstance
  apply Cochain.ext
  intro p q hpq
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  ext x
  refine (applyHomSection_restrict Rc H (leOfHom V.unop.hom) n p q hpq s x).trans ?_
  refine (h p q hpq V.unop.left (leOfHom V.unop.hom) x).trans ?_
  exact (applyHomSection_restrict Rc H (leOfHom V.unop.hom) n p q hpq t x).symm

/-- The composition morphism of internal Hom complexes on the ringed space, read off from the
ringed site of its opens. -/
noncomputable abbrev homComplexComposition
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    tensorTotal Rc (sheafHomComplex Rc L M).obj (sheafHomComplex Rc K L).obj ⟶
      (sheafHomComplex Rc K M).obj :=
  (Stacks.Cohomology.compositionConstruction (ringedSite Rc)).comp K L M

/-- The composition morphism acts on a homogeneous local pure tensor by composition, stated at
an arbitrary total degree. -/
private lemma homComplexComposition_tmul
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X)
    (p q r s n : ℤ) (hrs : r + q = s) (hn : s + p = n)
    (β : ((sheafHomComplex Rc L M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex Rc K L).obj.X q).val.obj (op U))
    (x : (K.X r).val.obj (op U)) :
    applyHomSection Rc (sheafHomComplex Rc K M) U (p + q) r n (by omega)
        (((homComplexComposition Rc K L M).f (p + q)).val.app (op U)
          (tensorTotalSection Rc (sheafHomComplex Rc L M).obj
            (sheafHomComplex Rc K L).obj U p q β γ)) x =
      applyHomSection Rc (sheafHomComplex Rc L M) U p s n hn β
        (applyHomSection Rc (sheafHomComplex Rc K L) U q r s hrs γ x) := by
  obtain rfl : n = r + q + p := by omega
  exact (Stacks.Cohomology.compositionConstruction (ringedSite Rc)).comp_tmul
    K L M U p q r s hrs hn β γ x

/-- Evaluating the image of a local section under the canonical internal Hom map is evaluating
the section itself, pre- and postcomposed with the two morphisms. -/
private lemma applyHomSection_sheafHomComplexMap
    {K K' I I' : CochainComplex (StructureSheafModules Rc) ℤ} (g : K' ⟶ K) (f : I' ⟶ I)
    (U : Opens X) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex Rc K I').obj.X n).val.obj (op U)) (x : (K'.X p).val.obj (op U)) :
    applyHomSection Rc (sheafHomComplex Rc K' I) U n p q hpq
        (((sheafHomComplexMap Rc g f).f n).val.app (op U) s) x =
      (f.f q).val.app (op U) (applyHomSection Rc (sheafHomComplex Rc K I') U n p q hpq s
        ((g.f p).val.app (op U) x)) :=
  applyHomSection_map Rc g f _ _ _ (sheafHomComplexMap_isInduced Rc g f) U n p q hpq s x

/-- Diagonal morphisms `Tot(K ⊗ SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗ L))`, specified by their
action on all homogeneous local pure tensors. -/
structure DiagonalBetterConstruction where
  /-- The diagonal morphism attached to three complexes. -/
  diagonal : (K L M : CochainComplex (StructureSheafModules Rc) ℤ) →
    tensorTotal Rc K (sheafHomComplex Rc M L).obj ⟶
      (sheafHomComplex Rc M (tensorTotal Rc K L)).obj
  /-- On every open set the morphism sends a homogeneous local pure tensor `k ⊗ φ` to the
  internal Hom section `m ↦ k ⊗ φ(m)`, with no sign. -/
  diagonal_tmul : ∀ (K L M : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X)
      (p q a b : ℤ) (hab : a + q = b)
      (k : (K.X p).val.obj (op U))
      (φ : ((sheafHomComplex Rc M L).obj.X q).val.obj (op U))
      (m : (M.X a).val.obj (op U)),
    applyHomSection Rc (sheafHomComplex Rc M (tensorTotal Rc K L)) U (p + q) a (p + b)
        (by omega)
        (((diagonal K L M).f (p + q)).val.app (op U)
          (tensorTotalSection Rc K (sheafHomComplex Rc M L).obj U p q k φ)) m =
      tensorTotalSection Rc K L U p b k
        (applyHomSection Rc (sheafHomComplex Rc M L) U q a b hab φ m)

/-- The diagonal morphism, as the composite of the diagonal morphism of [Stacks, Tag 0A8Q]
with the composition morphism of internal Hom complexes of [Stacks, Tag 0A91]. -/
noncomputable def diagonalBetterMorphism
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    tensorTotal Rc K (sheafHomComplex Rc M L).obj ⟶
      (sheafHomComplex Rc M (tensorTotal Rc K L)).obj :=
  tensorTotalMap Rc (diagonalTensorHom Rc K L) (𝟙 (sheafHomComplex Rc M L).obj) ≫
    homComplexComposition Rc M L (tensorTotal Rc K L)

/-- On a homogeneous local pure tensor `k ⊗ φ` the composite morphism is the internal Hom
section `m ↦ k ⊗ φ(m)`, with no sign. -/
theorem diagonalBetterMorphism_tmul
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) (U : Opens X)
    (p q a b : ℤ) (hab : a + q = b)
    (k : (K.X p).val.obj (op U))
    (φ : ((sheafHomComplex Rc M L).obj.X q).val.obj (op U))
    (m : (M.X a).val.obj (op U)) :
    applyHomSection Rc (sheafHomComplex Rc M (tensorTotal Rc K L)) U (p + q) a (p + b)
        (by omega)
        (((diagonalBetterMorphism Rc K L M).f (p + q)).val.app (op U)
          (tensorTotalSection Rc K (sheafHomComplex Rc M L).obj U p q k φ)) m =
      tensorTotalSection Rc K L U p b k
        (applyHomSection Rc (sheafHomComplex Rc M L) U q a b hab φ m) := by
  rw [diagonalBetterMorphism, comp_f_val_app, tensorTotalMap_section, id_f_val_app,
    homComplexComposition_tmul Rc M L (tensorTotal Rc K L) U p q a b (p + b) hab (by omega)]
  exact diagonalTensorHom_apply Rc K L U p b k _

/-- **Stacks 0BYR.** The canonical diagonal morphisms
`Tot(K ⊗ SheafHom(M, L)) ⟶ SheafHom(M, Tot(K ⊗ L))` for complexes of modules on a ringed
space, sending a homogeneous local pure tensor `k ⊗ φ` to the internal Hom section
`m ↦ k ⊗ φ(m)`. -/
@[stacks 0BYR "the canonical morphism"]
noncomputable def diagonalBetterConstruction : DiagonalBetterConstruction Rc where
  diagonal := diagonalBetterMorphism Rc
  diagonal_tmul := diagonalBetterMorphism_tmul Rc

/-- The canonical diagonal morphism attached to three complexes of modules. -/
noncomputable abbrev diagonalBetter
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    tensorTotal Rc K (sheafHomComplex Rc M L).obj ⟶
      (sheafHomComplex Rc M (tensorTotal Rc K L)).obj :=
  (diagonalBetterConstruction Rc).diagonal K L M

namespace DiagonalBetterConstruction

variable {Rc}

/-- Two morphisms from a total tensor product to an internal Hom complex are equal as soon as,
on every homogeneous local pure tensor, the two internal Hom sections they produce act in the
same way. -/
theorem hom_ext {A B M T : CochainComplex (StructureSheafModules Rc) ℤ}
    {f g : tensorTotal Rc A B ⟶ (sheafHomComplex Rc M T).obj}
    (h : ∀ (U : Opens X) (t r a c : ℤ) (hac : a + (t + r) = c)
        (x : (A.X t).val.obj (op U)) (y : (B.X r).val.obj (op U))
        (m : (M.X a).val.obj (op U)),
      applyHomSection Rc (sheafHomComplex Rc M T) U (t + r) a c hac
          ((f.f (t + r)).val.app (op U) (tensorTotalSection Rc A B U t r x y)) m =
        applyHomSection Rc (sheafHomComplex Rc M T) U (t + r) a c hac
          ((g.f (t + r)).val.app (op U) (tensorTotalSection Rc A B U t r x y)) m) :
    f = g := by
  refine tensorTotal_hom_ext Rc fun U t r x y => ?_
  refine homSection_ext_restrict Rc (sheafHomComplex Rc M T) U (t + r)
    fun a c hac V hVU m => ?_
  rw [← PresheafOfModules.naturality_apply (f.f (t + r)).val (homOfLE hVU).op,
    ← PresheafOfModules.naturality_apply (g.f (t + r)).val (homOfLE hVU).op,
    tensorTotalSection_restrict]
  exact h V t r a c hac _ _ m

/-- The characterisation on homogeneous local pure tensors determines the diagonal morphism:
any two diagonal morphisms for the same three complexes agree. -/
theorem diagonal_unique (D D' : DiagonalBetterConstruction Rc)
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    D.diagonal K L M = D'.diagonal K L M := by
  refine hom_ext fun U t r a c hac k φ m => ?_
  obtain rfl : c = t + (a + r) := by omega
  rw [D.diagonal_tmul K L M U t r a (a + r) rfl k φ m,
    D'.diagonal_tmul K L M U t r a (a + r) rfl k φ m]

/-- The diagonal morphism is covariant in the tensor factor. -/
theorem diagonal_natural_left (D : DiagonalBetterConstruction Rc)
    {K K' : CochainComplex (StructureSheafModules Rc) ℤ}
    (L M : CochainComplex (StructureSheafModules Rc) ℤ) (f : K ⟶ K') :
    D.diagonal K L M ≫ sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc f (𝟙 L)) =
      tensorTotalMap Rc f (𝟙 (sheafHomComplex Rc M L).obj) ≫ D.diagonal K' L M := by
  refine hom_ext fun U t r a c hac k φ m => ?_
  obtain rfl : c = t + (a + r) := by omega
  rw [comp_f_val_app, comp_f_val_app,
    applyHomSection_sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc f (𝟙 L)),
    id_f_val_app, D.diagonal_tmul K L M U t r a (a + r) rfl k φ m,
    tensorTotalMap_section, id_f_val_app,
    tensorTotalMap_section, id_f_val_app,
    D.diagonal_tmul K' L M U t r a (a + r) rfl _ φ m]

/-- The diagonal morphism is covariant in the target of the internal Hom complex. -/
theorem diagonal_natural_right (D : DiagonalBetterConstruction Rc)
    (K : CochainComplex (StructureSheafModules Rc) ℤ)
    {L L' : CochainComplex (StructureSheafModules Rc) ℤ}
    (M : CochainComplex (StructureSheafModules Rc) ℤ) (g : L ⟶ L') :
    D.diagonal K L M ≫ sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc (𝟙 K) g) =
      tensorTotalMap Rc (𝟙 K) (sheafHomComplexMap Rc (𝟙 M) g) ≫ D.diagonal K L' M := by
  refine hom_ext fun U t r a c hac k φ m => ?_
  obtain rfl : c = t + (a + r) := by omega
  rw [comp_f_val_app, comp_f_val_app,
    applyHomSection_sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc (𝟙 K) g),
    id_f_val_app, D.diagonal_tmul K L M U t r a (a + r) rfl k φ m,
    tensorTotalMap_section, id_f_val_app,
    tensorTotalMap_section, id_f_val_app,
    D.diagonal_tmul K L' M U t r a (a + r) rfl k _ m,
    applyHomSection_sheafHomComplexMap Rc (𝟙 M) g,
    id_f_val_app]

/-- The diagonal morphism is contravariant in the source of the internal Hom complex. -/
theorem diagonal_natural_hom (D : DiagonalBetterConstruction Rc)
    (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    {M M' : CochainComplex (StructureSheafModules Rc) ℤ} (h : M' ⟶ M) :
    D.diagonal K L M ≫ sheafHomComplexMap Rc h (𝟙 (tensorTotal Rc K L)) =
      tensorTotalMap Rc (𝟙 K) (sheafHomComplexMap Rc h (𝟙 L)) ≫ D.diagonal K L M' := by
  refine hom_ext fun U t r a c hac k φ m => ?_
  obtain rfl : c = t + (a + r) := by omega
  rw [comp_f_val_app, comp_f_val_app,
    applyHomSection_sheafHomComplexMap Rc h (𝟙 (tensorTotal Rc K L)),
    id_f_val_app, D.diagonal_tmul K L M U t r a (a + r) rfl k φ _,
    tensorTotalMap_section, id_f_val_app,
    D.diagonal_tmul K L M' U t r a (a + r) rfl k _ m,
    applyHomSection_sheafHomComplexMap Rc h (𝟙 L),
    id_f_val_app]

end DiagonalBetterConstruction

/-- **Stacks 0BYR.** The canonical diagonal morphism is covariant in the tensor factor. -/
@[stacks 0BYR "functoriality in the first complex"]
theorem diagonalBetter_natural_left
    {K K' : CochainComplex (StructureSheafModules Rc) ℤ}
    (L M : CochainComplex (StructureSheafModules Rc) ℤ) (f : K ⟶ K') :
    diagonalBetter Rc K L M ≫ sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc f (𝟙 L)) =
      tensorTotalMap Rc f (𝟙 (sheafHomComplex Rc M L).obj) ≫ diagonalBetter Rc K' L M :=
  (diagonalBetterConstruction Rc).diagonal_natural_left L M f

/-- **Stacks 0BYR.** The canonical diagonal morphism is covariant in the target of the
internal Hom complex. -/
@[stacks 0BYR "functoriality in the second complex"]
theorem diagonalBetter_natural_right
    (K : CochainComplex (StructureSheafModules Rc) ℤ)
    {L L' : CochainComplex (StructureSheafModules Rc) ℤ}
    (M : CochainComplex (StructureSheafModules Rc) ℤ) (g : L ⟶ L') :
    diagonalBetter Rc K L M ≫ sheafHomComplexMap Rc (𝟙 M) (tensorTotalMap Rc (𝟙 K) g) =
      tensorTotalMap Rc (𝟙 K) (sheafHomComplexMap Rc (𝟙 M) g) ≫ diagonalBetter Rc K L' M :=
  (diagonalBetterConstruction Rc).diagonal_natural_right K M g

/-- **Stacks 0BYR.** The canonical diagonal morphism is contravariant in the source of the
internal Hom complex. -/
@[stacks 0BYR "functoriality in the third complex"]
theorem diagonalBetter_natural_hom
    (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    {M M' : CochainComplex (StructureSheafModules Rc) ℤ} (h : M' ⟶ M) :
    diagonalBetter Rc K L M ≫ sheafHomComplexMap Rc h (𝟙 (tensorTotal Rc K L)) =
      tensorTotalMap Rc (𝟙 K) (sheafHomComplexMap Rc h (𝟙 L)) ≫ diagonalBetter Rc K L M' :=
  (diagonalBetterConstruction Rc).diagonal_natural_hom K L h

end Stacks.SheafOfModules

end
