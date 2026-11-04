module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import StacksCore.Tactic.StacksAttribute

/-! # The converse of Stacks 05VD along a pullback which preserves and reflects monomorphisms

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `G` a sheaf of
`O_D`-modules.  **Stacks 05VD** says that `G` flat implies `f^*G` flat.  This file proves the
**converse** under one hypothesis on the pullback of sheaves of modules along `f`: that it both
preserves and reflects monomorphisms.

## The argument

Flatness of `G` is exactness of `· ⊗_{O_D} G`, and its right-exactness half holds for every
sheaf of modules.  So by `Stacks.SheafOfModules.isFlat_of_mono_sheafTensorRight_map` all that is
needed is that `φ ⊗ 1_G` be a monomorphism whenever `φ` is the first map of a short exact
sequence.  **Stacks 03EL**, `Stacks.SheafOfModules.pullbackTensorIso`, is an isomorphism of
*bifunctors*, so fixing its right factor at `G` gives

`(· ⊗_{O_D} G) ⋙ f^* ≅ f^* ⋙ (· ⊗_{O_C} f^*G)`,

which is `pullbackSheafTensorRightIso` below.  The right-hand composite preserves monomorphisms:
`f^*` does by hypothesis, and `· ⊗_{O_C} f^*G` does because `f^*G` is flat.  Transporting along
the isomorphism, the left-hand composite preserves monomorphisms too; and since `f^*` reflects
them, `· ⊗_{O_D} G` preserves them.

Nothing here asks `f^*` to be an equivalence, and nothing asks it to be faithful: a left exact
functor which detects the zero object reflects monomorphisms
(`CategoryTheory.Functor.reflectsMonomorphisms_of_preservesFiniteLimits_of_reflectsZeroObjects`),
and that is the form in which the hypothesis is available at the comparison functors of Descent,
Proposition 03DX.  This is what distinguishes the results below from
`Stacks.Sheaves.LocalTypeComparison.isFlat_iff`, whose reverse half applies 05VD to the inverse
morphism and therefore needs `[f.toToposHom.pushforward.IsEquivalence]`.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackSheafTensorRightIso`: **Stacks 03EL with its right
  factor fixed**, as an isomorphism of endofunctor composites.
* `Stacks.Sheaves.RingedToposModules.isFlat_of_isFlat_pullbackModules`: **the converse of
  Stacks 05VD** for a pullback of sheaves of modules which preserves and reflects
  monomorphisms.
* `Stacks.Sheaves.RingedToposModules.isFlat_iff_pullbackModules_of_reflectsMonomorphisms`: the
  resulting equivalence, 05VD and its converse together.

## Implementation notes

The endofunctor whose exactness *is* flatness, in `Stacks.SheafOfModules.IsFlat`, is the
right-tensor functor `(Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj G`, while Tag 03EL
is stated for the tensor *bifunctor* of Tag 0GMW,
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor O)`.  The first is the second
with its right factor fixed, up to the identity morphism of that fixed factor which the
bifunctor composes in.  Each of the three identifications needed is isolated in its own lemma
below — `sheafTensorRight_comp_pullbackModules_map`,
`pullbackModules_comp_sheafTensorRight_map` and `prod_map_pullbackModules_id` — rather than left
to the unifier inside the proofs, because a proof which re-solves the identification at each
step against `Stacks.SheafOfModules.Tensor.sheafTensor` runs out of heartbeats.  Stated once
apiece each costs a `simp only` over the structural lemmas of `Functor.uncurry` and
`Functor.flip`, which never unfolds the tensor, and `pullbackSheafTensorRight_naturality` is then
an ordinary rewrite.

No `@[stacks 05VD]` attribute is claimed: 05VD is the forward implication, proved as
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules`, and its converse is not an assertion
of that tag.  Nor is `@[stacks 03EL]` claimed for `pullbackSheafTensorRightIso`, which is the
`Stacks.SheafOfModules.pullbackTensorIso` with one argument fixed.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u w v' u' w'

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-! ### The three identifications, each paid for once -/

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The pullback of the identity of `G`, paired with the pullback of `φ`, is the pullback of `φ`
paired with the identity of `f^*G`.  This is functoriality of `f^*` on identities, read in the
product category, and it is what turns the naturality square of Tag 03EL at `(φ, 1_G)` into a
statement about `· ⊗ f^*G`. -/
theorem prod_map_pullbackModules_id
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M N : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (φ : M ⟶ N) :
    (Prod.mkHom (f.pullbackModules.map φ) (f.pullbackModules.map (𝟙 G)) :
        ((f.pullbackModules.obj M, f.pullbackModules.obj G) :
          _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
          _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
          (f.pullbackModules.obj N, f.pullbackModules.obj G)) =
      Prod.mkHom (f.pullbackModules.map φ) (𝟙 (f.pullbackModules.obj G)) :=
  Prod.hom_ext rfl (f.pullbackModules.map_id G)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- `(· ⊗_{O_D} G) ⋙ f^*` acts on a morphism as the Tag 0GMW tensor bifunctor followed by `f^*`
does on that morphism paired with the identity of `G`. -/
theorem sheafTensorRight_comp_pullbackModules_map
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M N : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (φ : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G ⋙ f.pullbackModules).map φ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
          f.pullbackModules).map
        (Prod.mkHom φ (𝟙 G) :
          ((M, G) : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ×
            _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⟶ (N, G)) := by
  simp only [Functor.comp_map, Functor.flip_obj_map, Functor.uncurry_obj_map, Prod.mkHom,
    CategoryTheory.Functor.map_id, Category.comp_id]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `f^* ⋙ (· ⊗_{O_C} f^*G)` acts on a morphism as the Tag 0GMW tensor bifunctor does on its
pullback paired with the identity of `f^*G`. -/
theorem pullbackModules_comp_sheafTensorRight_map
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M N : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (φ : M ⟶ N) :
    (f.pullbackModules ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        (f.pullbackModules.obj G)).map φ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O)).map
        (Prod.mkHom (f.pullbackModules.map φ) (𝟙 (f.pullbackModules.obj G)) :
          ((f.pullbackModules.obj M, f.pullbackModules.obj G) :
            _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ×
            _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
            (f.pullbackModules.obj N, f.pullbackModules.obj G)) := by
  simp only [Functor.comp_map, Functor.flip_obj_map, Functor.uncurry_obj_map, Prod.mkHom,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-! ### Stacks 03EL with its right factor fixed -/

/-- **The naturality square of Tag 03EL with its right factor fixed at `G`.**  The comparison
`f^*(M ⊗_{O_D} G) ≅ f^*M ⊗_{O_C} f^*G` is natural in `M`. -/
theorem pullbackSheafTensorRight_naturality
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M N : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (φ : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G ⋙ f.pullbackModules).map φ ≫
        (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (N, G) =
      (Stacks.SheafOfModules.pullbackTensorIso f).hom.app (M, G) ≫
        (f.pullbackModules ⋙ (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
          (f.pullbackModules.obj G)).map φ := by
  rw [sheafTensorRight_comp_pullbackModules_map f G φ,
    pullbackModules_comp_sheafTensorRight_map f G φ, ← prod_map_pullbackModules_id f G φ]
  exact (Stacks.SheafOfModules.pullbackTensorIso f).hom.naturality (Prod.mkHom φ (𝟙 G))

/-- **Stacks 03EL with its right factor fixed at `G`**, as an isomorphism of endofunctor
composites:

`(· ⊗_{O_D} G) ⋙ f^* ≅ f^* ⋙ (· ⊗_{O_C} f^*G)`.

The components are those of `Stacks.SheafOfModules.pullbackTensorIso` and the naturality is
`pullbackSheafTensorRight_naturality`. -/
def pullbackSheafTensorRightIso
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G ⋙ f.pullbackModules ≅
      f.pullbackModules ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj (f.pullbackModules.obj G) :=
  NatIso.ofComponents (fun M => (Stacks.SheafOfModules.pullbackTensorIso f).app (M, G))
    (fun φ => pullbackSheafTensorRight_naturality f G φ)

/-! ### The converse of Stacks 05VD -/

/-- **The converse of Stacks 05VD, for a pullback of sheaves of modules which preserves and
reflects monomorphisms.**  If `f^*G` is a flat `O_C`-module then `G` is a flat `O_D`-module.

The two hypotheses on `f^*` are what replaces the equivalence hypothesis of
`Stacks.Sheaves.LocalTypeComparison.isFlat_iff`: preservation of monomorphisms is part of left
exactness, and reflection of monomorphisms follows from left exactness together with detection
of the zero object. -/
theorem isFlat_of_isFlat_pullbackModules [HasSheafify Y.J AddCommGrpCat.{w'}]
    [f.pullbackModules.PreservesMonomorphisms] [f.pullbackModules.ReflectsMonomorphisms]
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (h : Stacks.SheafOfModules.IsFlat (O := X.O) (f.pullbackModules.obj G)) :
    Stacks.SheafOfModules.IsFlat (O := Y.O) G := by
  have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
      (f.pullbackModules.obj G)) := h.1
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
      (f.pullbackModules.obj G)).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G ⋙
      f.pullbackModules).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (pullbackSheafTensorRightIso f G).symm
  refine Stacks.SheafOfModules.isFlat_of_mono_sheafTensorRight_map Y.O G fun T hT => ?_
  have : Mono T.f := hT.mono_f
  exact Functor.ReflectsMonomorphisms.reflects (F := f.pullbackModules) _
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).flip.obj G ⋙ f.pullbackModules).map_mono T.f)

/-- **Stacks 05VD and its converse**, for a pullback of sheaves of modules which preserves and
reflects monomorphisms: a sheaf of `O_D`-modules is flat if and only if its pullback is flat.

The forward implication is Stacks 05VD, `isFlat_pullbackModules`, which needs neither
hypothesis; the reverse one is `isFlat_of_isFlat_pullbackModules`. -/
theorem isFlat_iff_pullbackModules_of_reflectsMonomorphisms
    [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
    [HasSheafify Y.J AddCommGrpCat.{w'}]
    [f.pullbackModules.PreservesMonomorphisms] [f.pullbackModules.ReflectsMonomorphisms]
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    Stacks.SheafOfModules.IsFlat (O := Y.O) G ↔
      Stacks.SheafOfModules.IsFlat (O := X.O) (f.pullbackModules.obj G) :=
  ⟨isFlat_pullbackModules f G, isFlat_of_isFlat_pullbackModules f G⟩

end Stacks.Sheaves.RingedToposModules

end
