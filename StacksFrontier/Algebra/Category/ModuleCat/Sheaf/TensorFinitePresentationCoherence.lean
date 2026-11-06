module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness

/-!
# Coherence of the tensor product of a finitely presented sheaf with a coherent sheaf

Stacks 03L6 asserts that the tensor product of two sheaves of modules on a ringed site inherits
each of the local finiteness properties of Stacks 03DL from its two factors.  This file proves
the mixed clause: the tensor product of a sheaf of modules of finite presentation with a
coherent sheaf of modules is coherent, where coherence is `SheafOfModules.IsCoherentOnSite`,
Stacks 03DL(8).

## Main definitions

* `Stacks.SheafOfModules.TensorLocalProperties.tensorStructureSheafIso`: tensoring a sheaf of
  modules with the structure sheaf gives back that sheaf.
* `Stacks.SheafOfModules.TensorLocalProperties.tensorSwapTensorLeftIso`: the tensor product
  `F ⊗ G`, formed by the bifunctor, is the value at `F` of the functor "tensor on the left
  by `G`".

## Main results

* `Stacks.SheafOfModules.TensorLocalProperties.isCoherentOnSite_tensorLeft_free`: tensoring a
  coherent sheaf of modules with a free sheaf of modules of finite rank gives a coherent sheaf
  of modules.
* `Stacks.SheafOfModules.TensorLocalProperties.isCoherentOnSite_tensorSheaf_of_presentation`:
  the tensor product of a sheaf of modules admitting a finite *global* presentation with a
  coherent sheaf of modules is coherent.
* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isCoherent_of_isFinitePresentation`:
  **the tensor product of a sheaf of modules of finite presentation with a coherent sheaf of
  modules on a ringed site is coherent.**  This is Stacks 03L6 for the mixed
  finite-presentation/coherence clause.

## Implementation notes

The argument is the source's.  Locally `F` is the cokernel of a map of free sheaves of modules
of finite rank, so `F ⊗ G` is locally the cokernel of a map between finite direct sums of
copies of `G`; finite direct sums and cokernels of coherent sheaves of modules are coherent,
and coherence is local on the site.

Three inputs are taken from elsewhere and are not redone here.

* **Right exactness.**  `Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits`,
  Stacks 05NB, says that tensoring on the left by a fixed sheaf of modules preserves all small
  colimits.  It is the *left* factor that is fixed there, so the presentation of `F` is fed to
  it in the second variable and the result is compared with the bifunctor by
  `tensorSwapTensorLeftIso`, which is the braiding of presheaves of modules followed by
  sheafification.  Since the braiding is used only to compare two objects, and coherence is
  invariant under isomorphism, none of its coherence identities are needed.
* **Finite direct sums.**  `Stacks.SheafOfModules.isCoherentOnSite_sigma` is Stacks 01BY (3)
  for a coproduct of a finite family of coherent sheaves.  Tensoring on the left by `G` carries
  `SheafOfModules.free ι`, which is by definition a coproduct of copies of the structure sheaf,
  to a coproduct of copies of `G ⊗ 𝒪 ≅ G`.
* **Cokernels.**  `Stacks.SheafOfModules.isCoherentOnSite_cokernel` is Stacks 01BY (3) for
  cokernels, and `CategoryTheory.Limits.PreservesCokernel.iso` identifies the image of a
  cokernel under a colimit-preserving functor with the cokernel of the image.  The latter needs
  the functor to preserve zero morphisms, which follows from preservation of the initial object
  and hence from preservation of colimits.

**The hypotheses are exactly those of the finite-type and the locally-generated clauses.**  In
particular `HasSheafify J AddCommGrpCat`, which `SheafOfModules.Presentation.isColimit`
requires, is not assumed: it follows from the weak sheafification and local bijectivity
hypotheses by `AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness`.  No hypothesis about the
slices of the slice sites is needed, because the coherence predicate on a slice site is a
statement in the same vocabulary as on the site itself and its locality is a theorem,
`Stacks.SheafOfModules.isCoherentOnSite_of_coversTop`.

The covering furnished by `SheafOfModules.IsFinitePresentation` is indexed in the universe of
the site, whereas `isCoherentOnSite_of_coversTop` takes a covering family indexed in
`Type (max u v)`; the index type is therefore raised by `ULift`, which changes neither the
family of objects nor the sieve it generates.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite


namespace Stacks.SheafOfModules.TensorLocalProperties

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Tensoring with the structure sheaf is the identity.**  The underlying presheaf of modules
of the structure sheaf is the unit of the monoidal structure on presheaves of modules, so the
right unitor identifies the tensor-product presheaf with the presheaf underlying `M`, and the
counit of the sheafification adjunction identifies its sheafification with `M`. -/
noncomputable def tensorStructureSheafIso (O : Sheaf J CommRingCat.{w})
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj M).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit).app M

/-- **The tensor product of two sheaves of modules, read as a functor of its first variable.**
`TensorColimits.tensorLeft J O G` fixes `G` as the *left* factor, so its value at `F` is
`G ⊗ F`; this is the comparison with `F ⊗ G` as formed by the bifunctor, obtained from the
braiding of presheaves of modules by sheafification. -/
noncomputable def tensorSwapTensorLeftIso (O : Sheaf J CommRingCat.{w})
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G).obj F :=
  letI : SymmetricCategory (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := O.obj)
  (PresheafOfModules.sheafification
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).mapIso (β_ F.val G.val)

/-- **The tensor product of a coherent sheaf of modules with a free sheaf of modules of finite
rank is coherent.**  Tensoring on the left by `G` preserves the coproduct of copies of the
structure sheaf that defines `SheafOfModules.free ι`, and each factor becomes `G` by
`tensorStructureSheafIso`, so the result is a coproduct of finitely many copies of `G`. -/
theorem isCoherentOnSite_tensorLeft_free (O : Sheaf J CommRingCat.{w})
    (G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hG : _root_.SheafOfModules.IsCoherentOnSite G) (ι : Type w) [Finite ι] :
    _root_.SheafOfModules.IsCoherentOnSite
      (((Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G).obj
        (_root_.SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf O) ι)) := by
  let L := (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G
  have hL : PreservesColimitsOfSize.{w, w} L :=
    TensorColimits.tensorLeft_preservesColimits J O G
  exact isCoherentOnSite_of_iso
    ((PreservesCoproduct.iso L
        (fun _ : ι => _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) ≪≫
      Sigma.whiskerEquiv (Equiv.refl ι)
        (fun _ => (tensorStructureSheafIso O G).symm)).symm)
    (isCoherentOnSite_sigma (fun _ : ι => G) (fun _ => hG))

/-- **The tensor product of a globally finitely presented sheaf of modules with a coherent sheaf
of modules is coherent.**

`F` is the cokernel of a map `f` between free sheaves of modules on the index types of the
presentation, both finite; tensoring on the left by `G` preserves that cokernel, and both
`G ⊗ free` are coherent by `isCoherentOnSite_tensorLeft_free`, so the cokernel of `G ⊗ f` is
coherent by Stacks 01BY (3) for cokernels. -/
theorem isCoherentOnSite_tensorSheaf_of_presentation (O : Sheaf J CommRingCat.{w})
    {F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (P : F.Presentation) [hP : P.IsFinite]
    (hG : _root_.SheafOfModules.IsCoherentOnSite G) :
    _root_.SheafOfModules.IsCoherentOnSite
      (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).obj G) := by
  have : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let Rsh := Stacks.SheafOfModules.Tensor.ringSheaf O
  let L := (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (O)).obj G
  have hL : PreservesColimitsOfSize.{w, w} L :=
    TensorColimits.tensorLeft_preservesColimits J O G
  let _ : PreservesColimitsOfSize.{0, 0} L := preservesColimitsOfSize_shrink L
  let f : _root_.SheafOfModules.free (R := Rsh) P.relations.I ⟶
      _root_.SheafOfModules.free (R := Rsh) P.generators.I :=
    (_root_.SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  have eF : cokernel f ≅ F :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f 0)) P.isColimit
  have hcoker : _root_.SheafOfModules.IsCoherentOnSite (cokernel (L.map f)) :=
    isCoherentOnSite_cokernel (L.map f)
      (isCoherentOnSite_tensorLeft_free O G hG P.relations.I)
      (isCoherentOnSite_tensorLeft_free O G hG P.generators.I)
  exact isCoherentOnSite_of_iso (tensorSwapTensorLeftIso O F G).symm
    (isCoherentOnSite_of_iso ((PreservesCokernel.iso L f).symm ≪≫ L.mapIso eF) hcoker)

/-- **Stacks Project, Tag 03L6, finite presentation against coherence.**  The tensor product of
a sheaf of modules of finite presentation with a coherent sheaf of modules on a ringed site is
coherent.

Following the source: `F` admits a finite presentation over each member of a covering family,
the restriction of `G` to such a member is still coherent, and the tensor product formed on the
slice site is the restriction of the global one by
`Stacks.SheafOfModules.TensorLocalProperties.tensorOverIso`; so
`isCoherentOnSite_tensorSheaf_of_presentation` applies on each member, and coherence is local on
the site. -/
@[stacks 03L6 "fp_tensor_coherent", instance]
theorem tensorSheaf_isCoherent_of_isFinitePresentation
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F G : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [_root_.SheafOfModules.IsFinitePresentation F]
    [hG : _root_.SheafOfModules.IsCoherentOnSite G] :
    _root_.SheafOfModules.IsCoherentOnSite
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G) := by
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  refine isCoherentOnSite_of_coversTop _ (fun i : ULift.{v} q.I => q.X i.down) ?_ ?_
  · intro Z
    have hS : Sieve.ofObjects (fun i : ULift.{v} q.I => q.X i.down) Z =
        Sieve.ofObjects q.X Z := by
      ext Y f
      rw [Sieve.mem_ofObjects_iff, Sieve.mem_ofObjects_iff]
      exact ⟨fun ⟨i, hi⟩ => ⟨i.down, hi⟩, fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩⟩
    simpa [hS] using q.coversTop Z
  · intro i
    exact isCoherentOnSite_of_iso (tensorOverIso X.O (q.X i.down) F G)
      (isCoherentOnSite_tensorSheaf_of_presentation (X.O.over (q.X i.down))
        (q.presentation i.down) (hP := hq.isFinite_presentation i.down)
        (isCoherentOnSite_over G hG (q.X i.down)))

end Stacks.SheafOfModules.TensorLocalProperties

end
