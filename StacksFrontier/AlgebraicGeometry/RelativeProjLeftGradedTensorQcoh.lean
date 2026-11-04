module

public import StacksFrontier.AlgebraicGeometry.RelativeProjLeftGradedTensor
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The relative tensor product of graded modules on a scheme is quasi-coherent in each degree

Let `X` be a scheme, let `A` be a sheaf of graded algebras over its structure sheaf, let `P` be a
right graded `A`-module and let `N` be a left graded `A`-module, and suppose the homogeneous
pieces of `A`, of `P` and of `N` are quasi-coherent. This file proves that every homogeneous
piece of the relative tensor product `P ⊗_A N` is quasi-coherent.

Degree `n` of `P ⊗_A N` is, by construction, the associated sheaf of the cokernel of the balance
map `⨁_{r+s+t=n} P^r ⊗_O A^s ⊗_O N^t → ⨁_{p+q=n} P^p ⊗_O N^q` of presheaves of modules. Three
closure properties of quasi-coherence therefore suffice, and all three are already available:
the tensor product of two quasi-coherent modules is quasi-coherent (Tag 01CE), and
quasi-coherent modules on a scheme are closed under colimits, hence under coproducts and
cokernels (Tag 01BE). What this file supplies is the passage across the sheafification: the
coproducts and the cokernel are formed in presheaves of modules and sheafified afterwards, so
the colimit closure has to be applied to the image under sheafification of a colimit cocone
rather than to a colimit in sheaves.

This is the result property (6) of Tag 01O7 needs. That property compares `ℳ̃ ⊗ 𝒩̃` with
`(ℳ ⊗_𝒜 𝒩)~` for two left graded `𝒜`-modules in Situation 01NN, and the associated module on the
relative `Proj` is defined only for a graded module whose homogeneous pieces are quasi-coherent.
The last section of this file instantiates the result at Situation 01NN and forms `(ℳ ⊗_𝒜 𝒩)~`.

## Main results

* `Stacks.GradedRelativeTensor.isQuasicoherent_gradedTensor`: **every homogeneous piece of the
  relative tensor product of two graded modules with quasi-coherent pieces, over a graded
  algebra with quasi-coherent pieces, is quasi-coherent.**
* `Stacks.RelativeProj.Situation.isQuasicoherent_leftGradedTensor_piece`: the same for the
  tensor product `ℳ ⊗_𝒜 𝒩` of two left graded modules in Situation 01NN, as an instance.

## Main definitions

* `Stacks.GradedRelativeTensor.sheafify` is the sheafification of presheaves of `𝒪_X`-modules,
  and `Stacks.GradedRelativeTensor.sheafifyValIso` identifies the sheafification of the presheaf
  underlying a sheaf of modules with that sheaf.
* `Stacks.RelativeProj.Situation.tensorModuleSheaf` is **`(ℳ ⊗_𝒜 𝒩)~`**, the associated module
  on the relative projective spectrum of the tensor product of two left graded `𝒜`-modules.

## Implementation notes

The structure sheaf of rings is written `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`
throughout, not `AlgebraicGeometry.Scheme.ringCatSheaf X`, although the two are equal by `rfl`.
The reason is instance resolution, which is syntactic: sheafification of presheaves of modules
asks for `CategoryTheory.Presheaf.IsLocallyInjective` and `IsLocallySurjective` of the identity
of the presheaf of rings, and those instances are found at the `ringSheaf` spelling and not at
`ringCatSheaf`, whose underlying presheaf is hidden behind `sheafCompose`.

The construction of the relative tensor product and the quasi-coherence of a tensor product of
sheaves of modules are phrased over two different tensor products — the universe-polymorphic
objectwise `PresheafOfModules.tensorObj` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafificationTensor.lean`, and the ringed-space
`Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorStalkRingedSpace.lean`. On a scheme they
agree on the nose: `presheafTensor X.toRingedSpace F.val G.val = tensorObj F.val G.val` and
`TensorStalkRingedSpace.sheafifyFunctor X.toRingedSpace = sheafify X` are both `rfl`, so Tag
01CE applies to the sheafified objectwise tensor product with no comparison morphism at all.
That is why `isQuasicoherent_sheafifyTensorObjVal` below has a one-term proof.

For a summand of the balance map's source the two factors are not both underlying presheaves of
sheaves of modules: the summand is `P^r ⊗_O (A^s ⊗_O N^t)`, whose right-hand factor is itself a
presheaf tensor product. The step that handles this is Tag 0GMW,
`PresheafOfModules.sheafificationTensorIso`, which identifies the associated sheaf of an
objectwise tensor product with the tensor product of the associated sheaves; applied at the
identity morphism of the structure sheaf it reduces the summand to an iterated tensor product of
sheaves of modules.

The quasi-coherence hypotheses on the homogeneous pieces are explicit arguments rather than
instance arguments. A hypothesis of the form `∀ n : ℤ, (A.piece n).IsQuasicoherent` is not
synthesized by instance search from the per-degree instances that Situation 01NN carries, and
an instance argument also forces the subject's ring sheaf to be matched syntactically, which
fails across the two spellings described above.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01BE](https://stacks.math.columbia.edu/tag/01BE)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
open TopologicalSpace

universe u

namespace Stacks.GradedRelativeTensor

variable (X : Scheme.{u})

/- The structure sheaf of rings of a scheme, presented as the sheaf of rings underlying its
sheaf of commutative rings. This is `AlgebraicGeometry.Scheme.ringCatSheaf` on the nose; the
spelling matters only to instance resolution, as described in the implementation notes. -/
local macro "𝒪ˢ[" X:term "]" : term =>
  `(Stacks.SheafOfModules.Tensor.ringSheaf ($X).sheaf)

/-- Sheafification of presheaves of `𝒪_X`-modules on a scheme. This is the functor that degree
`n` of a relative tensor product is the image of. -/
noncomputable abbrev sheafify :
    PresheafOfModules.{u} (𝒪ˢ[X]).obj ⥤
      SheafOfModules.{u} 𝒪ˢ[X] :=
  PresheafOfModules.sheafification (R := 𝒪ˢ[X]) (𝟙 (𝒪ˢ[X]).obj)

/-- **The sheafification of the presheaf underlying a sheaf of modules is that sheaf**: the
counit of the sheafification adjunction, which is an isomorphism because a sheaf of modules is
determined by its underlying presheaf. -/
noncomputable def sheafifyValIso (M : SheafOfModules.{u} 𝒪ˢ[X]) :
    (sheafify X).obj M.val ≅ M :=
  (@asIso _ _ _ _ ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (𝒪ˢ[X]).obj)).counit) inferInstance).app M

/-- The sheafification of the presheaf underlying a quasi-coherent sheaf of modules is
quasi-coherent. -/
theorem isQuasicoherent_sheafifyVal (M : SheafOfModules.{u} 𝒪ˢ[X])
    (hM : M.IsQuasicoherent) : ((sheafify X).obj M.val).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent 𝒪ˢ[X]).prop_of_iso (sheafifyValIso X M).symm hM

/-- **Tag 01CE at the objectwise spelling.** The associated sheaf of the objectwise tensor
product of the presheaves underlying two quasi-coherent sheaves of modules is quasi-coherent:
that associated sheaf is the tensor product of sheaves of modules of Tag 01CA on the nose. -/
theorem isQuasicoherent_sheafifyTensorObjVal (F G : SheafOfModules.{u} 𝒪ˢ[X])
    (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    ((sheafify X).obj (PresheafOfModules.tensorObj F.val G.val)).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent X.toRingedSpace F G hF hG

/-- **The associated sheaf of an objectwise tensor product of presheaves of modules is
quasi-coherent as soon as the associated sheaves of the two factors are.** Neither factor need
be the presheaf underlying a sheaf of modules, which is what makes this applicable to a summand
`P^r ⊗_O (A^s ⊗_O N^t)` of the source of a balance map. -/
theorem isQuasicoherent_sheafifyTensorObj (P Q : PresheafOfModules.{u} (𝒪ˢ[X]).obj)
    (hP : ((sheafify X).obj P).IsQuasicoherent) (hQ : ((sheafify X).obj Q).IsQuasicoherent) :
    ((sheafify X).obj (PresheafOfModules.tensorObj P Q)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent 𝒪ˢ[X]).prop_of_iso
    ((PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj)).app (P, Q))
    (isQuasicoherent_sheafifyTensorObjVal X ((sheafify X).obj P) ((sheafify X).obj Q) hP hQ)

/-- **The associated sheaf of a coproduct of presheaves of modules whose associated sheaves are
quasi-coherent is quasi-coherent.** Sheafification is a left adjoint, so it carries the
coproduct cocone to a colimit cocone, and quasi-coherent modules on a scheme are closed under
colimits. -/
theorem isQuasicoherent_sheafifySigmaObj {I : Type}
    (P : I → PresheafOfModules.{u} (𝒪ˢ[X]).obj) [HasCoproduct P]
    (h : ∀ i, ((sheafify X).obj (P i)).IsQuasicoherent) :
    ((sheafify X).obj (∐ P)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (D := Discrete.functor P ⋙ sheafify X) (fun i => h i.as)
    (isColimitOfPreserves (sheafify X) (coproductIsCoproduct P))

/-- **The associated sheaf of a cokernel of presheaves of modules whose associated sheaves are
quasi-coherent is quasi-coherent**, by the same argument as for a coproduct. -/
theorem isQuasicoherent_sheafifyCokernel
    {P Q : PresheafOfModules.{u} (𝒪ˢ[X]).obj} (f : P ⟶ Q)
    (hP : ((sheafify X).obj P).IsQuasicoherent) (hQ : ((sheafify X).obj Q).IsQuasicoherent) :
    ((sheafify X).obj (cokernel f)).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (D := parallelPair f 0 ⋙ sheafify X)
    (fun k => by obtain _ | _ := k <;> assumption)
    (isColimitOfPreserves (sheafify X) (cokernelIsCokernel f))

section Graded

open _root_.SheafOfModules

variable {X}
variable {A : GradedAlgebra.{u, u} 𝒪ˢ[X]} (P : GradedModule.{u, u, u} A)
  (N : LeftGradedModule.{u, u, u} A)
  (hA : ∀ n : ℤ, (A.piece n).IsQuasicoherent) (hP : ∀ n : ℤ, (P.piece n).IsQuasicoherent)
  (hN : ∀ n : ℤ, (N.piece n).IsQuasicoherent)

include hP hN in
/-- The associated sheaf of a summand `P^p ⊗_O N^q` of the target of a balance map is
quasi-coherent. -/
theorem isQuasicoherent_sheafifyTensorSummand {n : ℤ} (p : TensorIndex n) :
    ((sheafify X).obj
      (RelativeTensor.tensorSummand (Osharp := X.sheaf) P N p)).IsQuasicoherent :=
  isQuasicoherent_sheafifyTensorObjVal X _ _ (hP p.1.1) (hN p.1.2)

include hA hP hN in
/-- The associated sheaf of a summand `P^r ⊗_O A^s ⊗_O N^t` of the source of a balance map is
quasi-coherent. -/
theorem isQuasicoherent_sheafifyRelationSummand {n : ℤ} (i : RelationIndex n) :
    ((sheafify X).obj
      (RelativeTensor.relationSummand (Osharp := X.sheaf) P N i)).IsQuasicoherent :=
  isQuasicoherent_sheafifyTensorObj X _ _
    (isQuasicoherent_sheafifyVal X (P.piece i.1.1) (hP i.1.1))
    (isQuasicoherent_sheafifyTensorObjVal X _ _ (hA i.1.2.1) (hN i.1.2.2))

include hA hP hN in
/-- **Every homogeneous piece of the relative tensor product `P ⊗_A N` is quasi-coherent**, when
the homogeneous pieces of the graded algebra and of the two graded modules are. Degree `n` is
the associated sheaf of the cokernel of the balance map of degree `n`, whose source and target
are coproducts of objectwise tensor products of those pieces. -/
theorem isQuasicoherent_gradedTensor (n : ℤ) :
    (RelativeTensor.gradedTensor (Osharp := X.sheaf) P N n).IsQuasicoherent :=
  isQuasicoherent_sheafifyCokernel X (RelativeTensor.balanceMap (Osharp := X.sheaf) P N n)
    (isQuasicoherent_sheafifySigmaObj X _
      (isQuasicoherent_sheafifyRelationSummand P N hA hP hN))
    (isQuasicoherent_sheafifySigmaObj X _ (isQuasicoherent_sheafifyTensorSummand P N hP hN))

end Graded

end Stacks.GradedRelativeTensor

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (ℳ 𝒩 : SheafOfModules.LeftGradedModule.{u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] [∀ n : ℤ, (𝒩.piece n).IsQuasicoherent]

/-- **Every homogeneous piece of `ℳ ⊗_𝒜 𝒩` is quasi-coherent**, for two left graded
`𝒜`-modules with quasi-coherent pieces in Situation 01NN. The homogeneous pieces of `𝒜` are
quasi-coherent by the situation's own `isQuasicoherent` field, and the pieces of `ℳ` read as a
right graded module are those of `ℳ`. -/
instance isQuasicoherent_leftGradedTensor_piece (n : ℤ) :
    ((s.leftGradedTensor ℳ 𝒩).piece n).IsQuasicoherent :=
  Stacks.GradedRelativeTensor.isQuasicoherent_gradedTensor (X := s.base)
    (ℳ.toGradedModule s.mul_comm) 𝒩 (fun n => s.isQuasicoherent n)
    (fun n => inferInstanceAs (ℳ.piece n).IsQuasicoherent)
    (fun n => inferInstanceAs (𝒩.piece n).IsQuasicoherent) n

/-- **`(ℳ ⊗_𝒜 𝒩)~`**, the sheaf of modules attached on the relative projective spectrum to the
tensor product of two left graded `𝒜`-modules with quasi-coherent pieces. This is the target of
the comparison morphism of property (6) of Tag 01O7. -/
noncomputable abbrev tensorModuleSheaf : (relativeProj s).Modules :=
  moduleSheaf (s.leftGradedTensor ℳ 𝒩)

end Stacks.RelativeProj.Situation

end
