module

public import StacksFrontier.Homology.KFlat.AcyclicKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorHomInterchangeStrictlyPerfect
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.DiagonalTensorSheafHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# K-flatness of the internal Hom complex out of a strictly perfect complex

Let `(X, O_X)` be a ringed space and let `E` and `F` be complexes of `O_X`-modules with `E`
strictly perfect, so that **Stacks 08DM** represents the derived internal hom
`RSheafHom(E, F)` by the internal Hom complex `H = SheafHom(E, F)`. **Stacks 0GM5** asserts
that `H` is K-flat as soon as `F` is.

## Main results

* `Stacks.SheafOfModules.acyclic_sheafHomComplex_of_acyclic`: the internal Hom complex out of a
  strictly perfect complex into an acyclic complex is acyclic.
* `Stacks.SheafOfModules.diagonalBetter_eq_tensorHomInterchange`: the Stacks 0BYR comparison
  built on the space is the Stacks 0BYT interchange morphism of its ringed site of opens.
* `Stacks.SheafOfModules.quasiIso_diagonalBetter_of_isFiniteFreeSummand`: that comparison is a
  quasi-isomorphism at a strictly perfect source.
* `Stacks.SheafOfModules.isKFlat_sheafHomComplex_of_isKFlat`: **Stacks 0GM5**, K-flatness of
  the internal Hom complex.

## How the argument runs

For an acyclic complex `G` of `O_X`-modules the source considers the canonical morphism of
[Stacks, Tag 0BYR]

`γ : Tot(G ⊗_{O_X} SheafHom(E, F)) ⟶ SheafHom(E, Tot(G ⊗_{O_X} F))`,

observes that `Tot(G ⊗ F)` is acyclic because `F` is K-flat, concludes that the target of `γ`
is acyclic, and finally proves that `γ` is an isomorphism by induction on the length of `E`,
through the termwise split short exact sequence `0 → σ^{≥a+1}E → E → σ^{≤a}E → 0` of
Homology, Section [Stacks, Tag 0118]. Acyclicity of the source of `γ` is then exactly what
K-flatness of `SheafHom(E, F)` asks about.

Every step is proved here; nothing is assumed. Only the quasi-isomorphy of `γ` is used, which
is weaker than the invertibility the source proves, and that is
`quasiIso_diagonalBetter_of_isFiniteFreeSummand`. The dévissage behind it is not run again on
the space: it is
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`, which
carries it out on an arbitrary ringed site for an arbitrary tensor factor and an arbitrary
target, and whose two hypotheses are letter for letter the boundedness and termwise hypotheses
`hE` and `hterm` carried here. The transport is `diagonalBetter_eq_tensorHomInterchange`,
identifying `γ` with the Stacks 0BYT interchange morphism of the ringed site of the opens of
`X`. Note that acyclicity of `G` plays no part in any of this.

That identification needs proof rather than `rfl`. The two morphisms have the same source and
the same target definitionally, because `Stacks.SheafOfModules.tensorTotal` and
`Stacks.SheafOfModules.sheafHomComplex` are the ringed-site constructions read on
`Stacks.SheafOfModules.ringedSite`; but `Stacks.SheafOfModules.diagonalTensorHom`, the first of
the two factors of `γ`, is extracted from an existence statement by choice, so it is pinned
down only by its characterisation on homogeneous local pure tensors. Both morphisms send
`k ⊗ φ` to `m ↦ k ⊗ φ(m)` with no sign, and
`Stacks.SheafOfModules.DiagonalBetterConstruction.hom_ext` turns that agreement into the
equality of the two.

The acyclicity of the target of `γ` is proved outright, and that is
`acyclic_sheafHomComplex_of_acyclic`: the internal Hom complex out of a strictly perfect
source carries a quasi-isomorphism of targets to a quasi-isomorphism
(`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`, the engine of the
Stacks 08DM representation and the ringed-site form of the local statement
[Stacks, Tag 08C9]), the zero complex maps to an acyclic complex by a quasi-isomorphism, and
the internal Hom complex into the zero complex vanishes.

## Implementation notes

Strict perfectness of `E` is spelled exactly as in the Stacks 08DM carrier
`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso`: boundedness as the finiteness of
the set of degrees where `E` does not vanish, and the termwise condition as
`AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`, the universe-polymorphic spelling of "a
direct summand of a finite free module". The reasons that spelling is forced are in the
implementation notes of that file.

Two spellings of the total tensor-product complex occur and both are needed. K-flatness
`Stacks.SheafOfModules.IsKFlat` is stated against `Stacks.SheafOfModules.Tensor.tensorComplex`,
the total complex of the sheafified tensor double complex, while the Stacks 0BYR comparison is
stated against `Stacks.SheafOfModules.tensorTotal`, the total complex of the presheaf-level
double complex sheafified degreewise. The bridge is
`AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, read on the ringed site of the
opens of `X`, and it is applied twice: once to the tensor product with `F` and once to the
tensor product with the internal Hom complex.

Two spellings of the ring sheaf also occur, and that is why
`acyclic_sheafHomComplex_of_acyclic` hands the quasi-isomorphy of `0 ⟶ T` to
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand` positionally rather
than letting instance search find it. The statements here are read over
`Stacks.SheafOfModules.StructureSheafModules`, i.e. over
`Stacks.SheafOfModules.structureSheaf Rc`, which is
`(CategoryTheory.sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, while the ringed-site
statements are read over `AlgebraicGeometry.RingedSite.ringSheaf`, which is
`Stacks.SheafOfModules.Tensor.ringSheaf Rc`, the same sheaf written as an explicit pair. The
two are definitionally equal — proof irrelevance in the sheaf condition, after unfolding
`CategoryTheory.sheafCompose` — so unification identifies them, but instance search does not
unfold a plain definition and so does not see the local `QuasiIso (0 : 0 ⟶ T)` as an instance
of the one the ringed-site lemma asks for. Passing it as an argument puts the identification
back where unification can make it.

## References

* [Stacks Project, Tag 0GM5](https://stacks.math.columbia.edu/tag/0GM5)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0BYT](https://stacks.math.columbia.edu/tag/0BYT)
* [Stacks Project, Tag 08C9](https://stacks.math.columbia.edu/tag/08C9)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace ZeroObject

namespace Stacks.SheafOfModules

universe u

section Zero

variable (Y : RingedSite.{u, u, u})

/-- The internal Hom sheaf into a zero module is zero: a morphism into a zero object is the
zero morphism, so the sheaf of such morphisms has only the zero section. -/
theorem internalHomSheaf_isZero_of_isZero_target
    {A B : _root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)} (hB : IsZero B) :
    IsZero (RingedSite.internalHomSheaf Y A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  ext U s
  have hz := (_root_.SheafOfModules.overFunctor (Tensor.ringSheaf Y.O) U.unop).map_isZero hB
  exact congrArg _root_.SheafOfModules.Hom.val
    (hz.eq_of_tgt (⟨s⟩ : A.over U.unop ⟶ B.over U.unop)
      ⟨(0 : (RingedSite.internalHomSheaf Y A B).val.obj U)⟩)

/-- The internal Hom complex into a zero complex is zero: each of its terms is a product of
internal Hom sheaves into the zero terms of the target. -/
theorem sheafHomComplex_isZero_of_isZero_target
    (E : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ)
    {L : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf Y.O)) ℤ} (hL : IsZero L) :
    IsZero (RingedSite.sheafHomComplex Y E L).obj := by
  apply RingedSite.complex_isZero_of_terms
  intro n
  apply (IsZero.iff_id_eq_zero _).2
  refine RingedSite.homDegree_hom_ext Y n _ _ fun q => ?_
  exact (internalHomSheaf_isZero_of_isZero_target Y
    ((HomologicalComplex.eval _ _ (n - q)).map_isZero hL)).eq_of_tgt _ _

end Zero

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A zero complex of `O_X`-modules is acyclic. -/
theorem acyclic_of_isZero {K : CochainComplex (StructureSheafModules Rc) ℤ} (hK : IsZero K) :
    K.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (HomologicalComplex.homologyFunctor (StructureSheafModules Rc)
    (ComplexShape.up ℤ) i).map_isZero hK

/-- The zero morphism from the zero complex to an acyclic complex is a quasi-isomorphism: in
every degree both homologies vanish. -/
theorem quasiIso_zero_of_acyclic {T : CochainComplex (StructureSheafModules Rc) ℤ}
    (hT : T.Acyclic) :
    QuasiIso (0 : (0 : CochainComplex (StructureSheafModules Rc) ℤ) ⟶ T) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact StacksDraft.TotalComplexQuasiIso.isIso_of_isZero_of_isZero _
    ((HomologicalComplex.homologyFunctor (StructureSheafModules Rc)
      (ComplexShape.up ℤ) i).map_isZero (isZero_zero _))
    (hT i).isZero_homology

/-- **The internal Hom complex out of a strictly perfect complex into an acyclic complex is
acyclic.** The internal Hom complex out of `E` carries a quasi-isomorphism of targets to a
quasi-isomorphism when `E` is bounded with every term a direct summand of a finite free
`O_X`-module; applying that to the quasi-isomorphism from the zero complex to `T` compares
`SheafHom(E, T)` with `SheafHom(E, 0)`, which vanishes. -/
theorem acyclic_sheafHomComplex_of_acyclic
    (E T : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i))
    (hT : T.Acyclic) :
    (sheafHomComplex Rc E T).obj.Acyclic := by
  have hq : QuasiIso (0 : (0 : CochainComplex (StructureSheafModules Rc) ℤ) ⟶ T) :=
    quasiIso_zero_of_acyclic Rc hT
  have hmap := @RingedSite.homMap_quasiIso_of_isFiniteFreeSummand (ringedSite Rc) _ _
    (0 : (0 : CochainComplex (StructureSheafModules Rc) ℤ) ⟶ T) hq E hE hterm
  refine (HomologicalComplex.acyclic_iff_of_quasiIso _ hmap).1 ?_
  exact acyclic_of_isZero Rc
    (sheafHomComplex_isZero_of_isZero_target (ringedSite Rc) E (isZero_zero _))

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The Stacks 0BYR comparison on a ringed space is the Stacks 0BYT interchange morphism of
its ringed site of opens.** Both have source `Tot(K ⊗ SheafHom(M, L))` and target
`SheafHom(M, Tot(K ⊗ L))` — definitionally the same complexes, since `tensorTotal` and
`sheafHomComplex` on the space are the ringed-site constructions read on `ringedSite Rc` — and
both send a homogeneous local pure tensor `k ⊗ φ` to the internal Hom section `m ↦ k ⊗ φ(m)`
with no sign. They are not the same term: `diagonalTensorHom` is extracted from an existence
statement by choice, so the comparison is only pinned down by that characterisation, which is
what `Stacks.SheafOfModules.DiagonalBetterConstruction.hom_ext` turns into an equality. -/
theorem diagonalBetter_eq_tensorHomInterchange
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    diagonalBetter Rc K L M = RingedSite.tensorHomInterchange (ringedSite Rc) K L M := by
  refine DiagonalBetterConstruction.hom_ext fun U t r a c hac x y m => ?_
  obtain rfl : c = t + (a + r) := by omega
  refine Eq.trans
    ((diagonalBetterConstruction Rc).diagonal_tmul K L M U t r a (a + r) rfl x y m) ?_
  exact (RingedSite.tensorHomInterchange_applyHomSection (ringedSite Rc) K L M U t r a (a + r)
    (t + (a + r)) rfl (by omega) x y m).symm

/-- **The Stacks 0BYR comparison `Tot(G ⊗ SheafHom(E, F)) ⟶ SheafHom(E, Tot(G ⊗ F))` is a
quasi-isomorphism when `E` is strictly perfect**, for arbitrary `G` and `F`. This is the
dévissage on the length of `E` along the termwise split stupid filtration of Homology,
Section 0118; it is carried out on the ringed site of the opens of `X` in
`AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`, and
transported here by `diagonalBetter_eq_tensorHomInterchange`. No acyclicity of `G` is
needed. -/
theorem quasiIso_diagonalBetter_of_isFiniteFreeSummand
    (G F E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i)) :
    QuasiIso (diagonalBetter Rc G F E) := by
  rw [diagonalBetter_eq_tensorHomInterchange]
  exact RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand
    (ringedSite Rc) G F E hE hterm

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 0GM5.** In the situation of Stacks 08DM — `E` strictly perfect, so that the
internal Hom complex `H = SheafHom(E, F)` represents `RSheafHom(E, F)` — the complex `H` is
K-flat as soon as `F` is.

For an acyclic `G` the argument is: `F` is K-flat and `G` is acyclic, so `Tot(G ⊗ F)` is
acyclic; the internal Hom complex out of a strictly perfect source into an acyclic complex is
acyclic, so the target of the Stacks 0BYR comparison
`Tot(G ⊗ SheafHom(E, F)) ⟶ SheafHom(E, Tot(G ⊗ F))` is acyclic; that comparison is a
quasi-isomorphism at a strictly perfect source, by the dévissage along the termwise split
stupid filtration of Homology, Section 0118 on the ringed site of the opens of `X`
in `AlgebraicGeometry.RingedSite.tensorHomInterchange_quasiIso_of_isFiniteFreeSummand`; hence
its source is acyclic too, and that source is the total complex K-flatness of `H` asks
about. -/
@[stacks 0GM5 "the whole lemma on a ringed space: for E strictly perfect, written out as in \
  Definition 20.46.1 -- hE is 'E^i is zero for all but finitely many i' and hterm is 'E^i is a \
  direct summand of a finite free O_X-module for all i' -- and F K-flat (hF), the complex \
  sheafHomComplex E F is K-flat"]
theorem isKFlat_sheafHomComplex_of_isKFlat
    (E F : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i))
    (hF : IsKFlat Rc F) :
    IsKFlat Rc (sheafHomComplex Rc E F).obj := by
  intro G hG
  have h1 : (tensorTotal Rc G F).Acyclic :=
    (HomologicalComplex.acyclic_iff_of_quasiIso
      (RingedSite.tensorTotalIsoTensorComplex (ringedSite Rc) G F).hom inferInstance).2 (hF G hG)
  have h2 : (sheafHomComplex Rc E (tensorTotal Rc G F)).obj.Acyclic :=
    acyclic_sheafHomComplex_of_acyclic Rc E _ hE hterm h1
  have h3 : (tensorTotal Rc G (sheafHomComplex Rc E F).obj).Acyclic :=
    (HomologicalComplex.acyclic_iff_of_quasiIso _
      (quasiIso_diagonalBetter_of_isFiniteFreeSummand Rc G F E hE hterm)).2 h2
  exact (HomologicalComplex.acyclic_iff_of_quasiIso
    (RingedSite.tensorTotalIsoTensorComplex (ringedSite Rc) G
      (sheafHomComplex Rc E F).obj).hom inferInstance).1 h3

end Stacks.SheafOfModules

end
