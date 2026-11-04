module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# A tensor product of finite locally free sheaves of modules is finite locally free

Let `(C, 𝒪)` be a ringed site and let `F` and `G` be sheaves of `𝒪`-modules which are finite
locally free in the sense of [Stacks, Tag 01C6] (2): each admits local free presentations on a
family of objects covering the final object. Then so does `F ⊗_𝒪 G`, on the common refinement
of the two families, with index type the product of the two index types.

The common refinement is the content: `CategoryTheory.GrothendieckTopology` has no operation
combining two families covering the final object, so the family is built by hand, indexed by
triples consisting of a member of each of the two given families together with an object
admitting arrows to both.

## Main definitions

* `Stacks.SheafOfModules.localGeneratorsDataTensor`: the local generators data of a tensor
  product, on the common refinement of the two given families. This is the public form of the
  construction otherwise available only inside the proof of
  `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteType`.
* `Stacks.SheafOfModules.generatingSectionsOfIsoFree` and `Stacks.SheafOfModules.overIsoFree`:
  the local basis attached to an isomorphism onto a free module, and the restriction of such an
  isomorphism along an arrow of the site.
* `Stacks.SheafOfModules.tensorOverIsoFree`: over a member of the common refinement, the
  tensor product restricts to a free module on the product of the two index types.

## Main results

* `Stacks.SheafOfModules.coversTop_tensorRefinement`: the common refinement of two families
  covering the final object covers the final object.
* `Stacks.SheafOfModules.isLocallyFreeData_localGeneratorsDataTensor` and
  `isFiniteType_localGeneratorsDataTensor`: the local generators data of the tensor product
  consists of local bases, and its index types are finite when those of the two factors are;
  `nonempty_localGeneratorsDataTensor` says they are inhabited when those of both factors are.
* `Stacks.SheafOfModules.isFiniteLocallyFree_tensor`: **a tensor product of finite locally free
  sheaves of modules is finite locally free.**
* `Stacks.SheafOfModules.exists_isLocallyFreeData_nonempty_tensor`: the same carrying the
  inhabitedness of the index types, which is positivity of the rank.

Part (2) of Tag 03L6 itself — the same statement for the covering-family form of finite local
freeness, [Stacks, Tag 03DL] (2), which is the form the other parts are stated in — is
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree`. It is not derived from the
results here: the local-generators form below pins the section universe to `max u v`, whereas
Tag 03L6 is about an arbitrary ringed site, and the covering-refinement argument that part (1)
already runs gives part (2) at an arbitrary section universe with no slice hypotheses.

## Implementation notes

Local freeness of the tensor product is obtained from `Stacks.SheafOfModules.tensorIsoFree`,
which produces an isomorphism onto a free module directly, rather than by computing the
canonical map out of a free module and checking it is invertible. So no formula for the
projection of the resulting family of generating sections is needed: the family is transported
from the free module along that isomorphism, which makes its projection invertible by
`SheafOfModules.GeneratingSections.ofEpi_π`.

The three spellings of the tensor product in play — `Strict` monoidal `⊗`,
`Stacks.SheafOfModules.Tensor.sheafTensor` and
`Stacks.SheafOfModules.Tensor.sheafTensor` — and the three of the underlying sheaf of rings agree
by `rfl`, so nothing has to be transported between them.

The section universe is `max u v` throughout, because the common refinement is indexed by
objects of the site and the generating families it carries are indexed in the section universe;
the two indexings are compared, so the section universe has to admit the object and morphism
universes of the site.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  overMap_preservesColimits

section FromIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}} {M : _root_.SheafOfModules.{w} R} {D : Type w}

/-- A sheaf of modules isomorphic to a free one carries a family of generating sections which
is a local basis, on the index type of that free module. -/
def generatingSectionsOfIsoFree (e : M ≅ _root_.SheafOfModules.free D) :
    M.GeneratingSections :=
  (_root_.SheafOfModules.free.generatingSections D).ofEpi e.symm.hom

@[simp]
lemma generatingSectionsOfIsoFree_index (e : M ≅ _root_.SheafOfModules.free D) :
    (generatingSectionsOfIsoFree e).I = D := rfl

instance isIso_π_generatingSectionsOfIsoFree (e : M ≅ _root_.SheafOfModules.free D) :
    IsIso (generatingSectionsOfIsoFree e).π := by
  have h : IsIso ((_root_.SheafOfModules.free.generatingSections D).π ≫ e.symm.hom) :=
    inferInstance
  exact Eq.mpr (congrArg IsIso (_root_.SheafOfModules.GeneratingSections.ofEpi_π
    (_root_.SheafOfModules.free.generatingSections D) e.symm.hom)) h

instance isFiniteType_freeGeneratingSections (D : Type w) [Finite D] :
    (_root_.SheafOfModules.free.generatingSections (R := R) D).IsFiniteType where
  finite := inferInstanceAs (Finite D)

instance isFiniteType_generatingSectionsOfIsoFree (e : M ≅ _root_.SheafOfModules.free D)
    [Finite D] : (generatingSectionsOfIsoFree e).IsFiniteType where
  finite := inferInstanceAs (Finite D)

end FromIso

section Restrict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}} {M : _root_.SheafOfModules.{w} R} {V U : C}

/-- A local basis of a sheaf of modules on the slice over `U` restricts along an arrow
`f : V ⟶ U` to a local basis on the slice over `V`, with the same index type. -/
def overIsoFree (f : V ⟶ U) (D : Type w)
    (e : M.over U ≅ _root_.SheafOfModules.free D) :
    M.over V ≅ _root_.SheafOfModules.free D :=
  ((_root_.SheafOfModules.overFunctorMap R f).app M).symm
    ≪≫ (_root_.SheafOfModules.overMap R f).mapIso e
    ≪≫ (_root_.SheafOfModules.mapFreeIso (_root_.SheafOfModules.overMap R f) D
        (_root_.SheafOfModules.overMapUnitIso f).symm).symm

end Restrict

section Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (O : Sheaf J CommRingCat.{max u v})

/-- Over an object on which both factors have local bases, the tensor product restricts to a
free module on the product of the two index types. -/
def tensorOverIsoFree (V : C)
    (E F : _root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (I K : Type (max u v))
    (eE : E.over V ≅ _root_.SheafOfModules.free I)
    (eF : F.over V ≅ _root_.SheafOfModules.free K) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj E).obj F).over V
      ≅ _root_.SheafOfModules.free (I × K) :=
  (TensorLocalProperties.tensorOverIso O V E F).symm ≪≫ tensorIsoFree (J.over V) eE eF

variable {E F : _root_.SheafOfModules.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)}

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The common refinement of two families covering the final object** covers the final
object: it is indexed by triples consisting of a member of each family together with an object
admitting arrows to both. -/
lemma coversTop_tensorRefinement (qE : E.LocalGeneratorsData.{u})
    (qF : F.LocalGeneratorsData.{u}) :
    J.CoversTop (fun z : (Σ i : qE.I, Σ j : qF.I,
      {V : C // Nonempty ((V ⟶ qE.X i) × (V ⟶ qF.X j))}) => z.2.2.1) := by
  intro W
  exact J.transitive (qE.coversTop W) _ (by
    intro V f hf
    refine J.superset_covering ?_ (qF.coversTop V)
    intro Z g hg
    obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff qE.X f).mp hf
    obtain ⟨j, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff qF.X g).mp hg
    exact (Sieve.mem_ofObjects_iff _ (g ≫ f)).2 ⟨⟨i, j, Z, ⟨(g ≫ b, c)⟩⟩, ⟨𝟙 Z⟩⟩)

/-- **The local generators data of a tensor product**, on the common refinement of the two
given families, with index types the products of the two. -/
def localGeneratorsDataTensor (qE : E.LocalGeneratorsData.{u}) (qF : F.LocalGeneratorsData.{u})
    [qE.IsLocallyFreeData] [qF.IsLocallyFreeData] :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj E).obj F).LocalGeneratorsData.{u} where
  I := Σ i : qE.I, Σ j : qF.I, {V : C // Nonempty ((V ⟶ qE.X i) × (V ⟶ qF.X j))}
  X z := z.2.2.1
  coversTop := coversTop_tensorRefinement O qE qF
  generators z :=
    generatingSectionsOfIsoFree
      (tensorOverIsoFree O z.2.2.1 E F (qE.generators z.1).I (qF.generators z.2.1).I
        (overIsoFree (Classical.choice z.2.2.2).1 _ (asIso (qE.generators z.1).π).symm)
        (overIsoFree (Classical.choice z.2.2.2).2 _ (asIso (qF.generators z.2.1).π).symm))

instance isLocallyFreeData_localGeneratorsDataTensor
    (qE : E.LocalGeneratorsData.{u}) (qF : F.LocalGeneratorsData.{u})
    [qE.IsLocallyFreeData] [qF.IsLocallyFreeData] :
    (localGeneratorsDataTensor O qE qF).IsLocallyFreeData where
  isIso z := by
    dsimp only [localGeneratorsDataTensor]
    exact isIso_π_generatingSectionsOfIsoFree _

/-- The index types of `localGeneratorsDataTensor` are finite when those of both factors
are. -/
instance isFiniteType_localGeneratorsDataTensor
    (qE : E.LocalGeneratorsData.{u}) (qF : F.LocalGeneratorsData.{u})
    [qE.IsLocallyFreeData] [qF.IsLocallyFreeData] [qE.IsFiniteType] [qF.IsFiniteType] :
    (localGeneratorsDataTensor O qE qF).IsFiniteType where
  isFiniteType z := by
    have _ := (‹qE.IsFiniteType›.isFiniteType z.1).finite
    have _ := (‹qF.IsFiniteType›.isFiniteType z.2.1).finite
    refine ⟨?_⟩
    exact inferInstanceAs (Finite ((qE.generators z.1).I × (qF.generators z.2.1).I))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The index types of `localGeneratorsDataTensor` are inhabited when those of both factors
are. -/
lemma nonempty_localGeneratorsDataTensor
    (qE : E.LocalGeneratorsData.{u}) (qF : F.LocalGeneratorsData.{u})
    [qE.IsLocallyFreeData] [qF.IsLocallyFreeData]
    (hE : ∀ i, Nonempty (qE.generators i).I) (hF : ∀ j, Nonempty (qF.generators j).I)
    (z : (localGeneratorsDataTensor O qE qF).I) :
    Nonempty ((localGeneratorsDataTensor O qE qF).generators z).I :=
  ⟨((hE z.1).some, (hF z.2.1).some)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A tensor product of finite locally free sheaves of modules is finite locally free.** -/
theorem isFiniteLocallyFree_tensor
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{max u v, v, u} E)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{max u v, v, u} F) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{max u v, v, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj E).obj F) := by
  obtain ⟨qE, hqE, hqEf⟩ := hE.exists_isFiniteLocallyFreeData
  obtain ⟨qF, hqF, hqFf⟩ := hF.exists_isFiniteLocallyFreeData
  let _ := hqE
  let _ := hqF
  let _ := hqEf
  let _ := hqFf
  constructor
  exact ⟨localGeneratorsDataTensor O qE qF, inferInstance, inferInstance⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A tensor product of locally free sheaves of modules of positive rank is locally free of
positive rank**: local bases with inhabited index types give local bases with inhabited index
types. -/
theorem exists_isLocallyFreeData_nonempty_tensor
    (hE : ∃ q : E.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
      ∀ i, Nonempty (q.generators i).I)
    (hF : ∃ q : F.LocalGeneratorsData.{u}, q.IsLocallyFreeData ∧
      ∀ i, Nonempty (q.generators i).I) :
    ∃ q : (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj E).obj F).LocalGeneratorsData.{u},
      q.IsLocallyFreeData ∧ ∀ i, Nonempty (q.generators i).I := by
  obtain ⟨qE, hqE, hEn⟩ := hE
  obtain ⟨qF, hqF, hFn⟩ := hF
  let _ := hqE
  let _ := hqF
  exact ⟨localGeneratorsDataTensor O qE qF, inferInstance,
    nonempty_localGeneratorsDataTensor O qE qF hEn hFn⟩

end Tensor

end Stacks.SheafOfModules
