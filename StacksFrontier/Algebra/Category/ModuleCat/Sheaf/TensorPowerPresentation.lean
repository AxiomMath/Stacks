module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentGradedCoprod
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence of the tensor algebra of a quasi-coherent sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a quasi-coherent sheaf of `𝒪_X`-modules. Stacks Tag
01CL asserts that the tensor, exterior and symmetric algebras of `F` are again quasi-coherent.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentAlgebras` proves the exterior and the
symmetric assertion; this file proves the **tensor** assertion,
`Stacks.SheafOfModules.isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent`, and with it clause
(5) of Tag 01CK for the tensor powers, `Stacks.SheafOfModules.isQuasicoherent_tensorPower`.

## Main definitions

* `CategoryTheory.Limits.isCokernelCoprodDesc`: **a cokernel of `coprod.desc u₁ u₂` computed in
  two steps**, in an arbitrary category with zero morphisms and binary coproducts.
* `Stacks.SheafOfModules.tensorSheafRight` and `tensorSheafLeft`: the two variables of
  `Stacks.SheafOfModules.Tensor.sheafTensor` as endofunctors of
  `SheafOfModules (CategoryTheory.Sheaf.toRingCat J 𝒪♯)`; see the implementation notes for why
  the first is a retyping of `Stacks.sheafTensorRight` rather than that functor itself.
* `Stacks.SheafOfModules.tensorSheafCommIso` and `tensorSheafLeftIso`: **the symmetry of the
  tensor product of sheaves of modules**, componentwise and as a natural isomorphism between the
  two one-variable functors. This is the sheafification of `Stacks.tensorObjComm`.
* `Stacks.SheafOfModules.presentationTensorSheaf`: the presentation of `M ⊗ N` described in the
  implementation notes.

## Main results

* `PresheafOfModules.tensorHom_tensorCommHom`: naturality of the symmetry of the objectwise
  tensor product in both variables at once. `Stacks.tensorCommHom_comp_tensorRight_map` is the
  case where the first morphism is an identity.
* `Stacks.SheafOfModules.nonempty_presentation_tensorSheaf`: **the tensor product of two
  presented sheaves of modules is presented.** This is the part of Stacks 01CE the tensor
  assertion of 01CL needs, over an arbitrary site.
* `Stacks.SheafOfModules.nonempty_presentation_tensorPower` and
  `nonempty_presentation_tensorPower_over`: **a presentation of `F` presents every tensor power
  of `F`**, globally and over an object of the site.
* `Stacks.SheafOfModules.isQuasicoherent_tensorPower`: **clause (5) of Tag 01CK for the tensor
  powers** — each `Tⁿ(F)` of a quasi-coherent `F` is quasi-coherent.
* `Stacks.SheafOfModules.isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent`: **clause (1) of
  Tag 01CL for the tensor algebra.**

## Implementation notes

**The tensor powers.** The exterior and symmetric assertions rest on Tag 01CJ, which turns a
presentation `F₂ ⟶ F₁ ⟶ F ⟶ 0` of `F` by free sheaves of modules into a three-term presentation
`F₂ ⊗ Sym^{n-1}(F₁) ⟶ Symⁿ(F₁) ⟶ Symⁿ(F) ⟶ 0` of each symmetric power, and likewise for the
exterior powers (`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`). A
tensor power of a presented sheaf of modules is not presented by three terms: already `T²` needs
`(F₂ ⊗ F₁) ⊕ (F₁ ⊗ F₂) ⟶ F₁ ⊗ F₁ ⟶ F ⊗ F ⟶ 0`. As in Stacks, whose proof of 01CL(1) for `T(F)`
cites Tag 01CE rather than 01CJ, the argument is an induction on the degree:

* `Tⁿ⁺²(F)` is `F ⊗ Tⁿ⁺¹(F)` by definition (`SheafOfModules.tensorPower_add_two`), so it is
  enough to present a tensor product of two presented sheaves of modules, which is
  `Stacks.SheafOfModules.nonempty_presentation_tensorSheaf`;
* `T⁰(F)` is the structure sheaf and `T¹(F)` is `F`, both of which are presented already.

The induction uses the same presentation data at every degree, which is the uniformity Tag 01CL
needs: the open on which `F` is presented presents every tensor power, with no further shrinking.

**The presentation of a tensor product.** Given cokernel diagrams
`free ι₁ --f₁--> free σ₁ --g₁--> M ⟶ 0` and `free ι₂ --f₂--> free σ₂ --g₂--> N ⟶ 0`, the sheaf
`M ⊗ N` is the cokernel of `(free ι₁ ⊗ free σ₂) ⊕ (free σ₁ ⊗ free ι₂) ⟶ free σ₁ ⊗ free σ₂`, and
the three corners are free on `ι₁ × σ₂`, `σ₁ × ι₂` and `σ₁ × σ₂` by
`Stacks.SheafOfModules.freeTensorFreeIso`. It is assembled from three inputs:

* the tensor product preserves colimits in the first variable
  (`Stacks.preservesColimitsOfSize_sheafTensorRight`);
* it therefore preserves them in the second variable too, through the symmetry
  `Stacks.tensorObjComm` of the objectwise tensor product, sheafified here as
  `Stacks.SheafOfModules.tensorSheafCommIso`;
* a cokernel of a morphism out of a binary coproduct can be computed in two steps,
  `CategoryTheory.Limits.isCokernelCoprodDesc`. This is the formal content of the double-complex
  argument: `g₁ ⊗ 𝟙` is the cokernel of `f₁ ⊗ 𝟙`, and `𝟙 ⊗ g₂` is the cokernel of the composite
  `(free σ₁ ⊗ free ι₂) ⟶ (free σ₁ ⊗ free σ₂) ⟶ (M ⊗ free σ₂)` because the second factor is an
  epimorphism, so the composite `(g₁ ⊗ 𝟙) ≫ (𝟙 ⊗ g₂)` is the cokernel of the morphism out of the
  coproduct.

No exactness of coproducts, no Grothendieck axiom and no stalkwise argument enters.

**One spelling per statement, and three `def`s that fix it.** The tensor product of sheaves of
modules has two spellings: `Stacks.SheafOfModules.Tensor.sheafTensor Osharp`, over the ring
sheaf written `CategoryTheory.Sheaf.toRingCat J 𝒪♯`, and `Stacks.sheafTensorRight 𝒪♯ N`,
over `Stacks.commRingSheafToRingSheaf 𝒪♯`. The two are definitionally equal and agree on objects
by `rfl` (`Stacks.SheafOfModules.tensorSheafBifunctor_obj`), but they are different
discrimination-tree keys, so the colimit-preservation instance is not found at the
spelling the bifunctor uses, and — worse — a *composite* whose middle object is written one way
at its source and the other at its target is not type-correct at `implicit` transparency, after
which no rewrite may cross it. Three retypings remove the problem, each a `def` with an ascribed
type and never an `abbrev`:

* `tensorSheafRight` is `Stacks.sheafTensorRight` with source and target spelled over
  `toRingCat J 𝒪♯`;
* `tensorSheafRightMapLeft` is `tensorSheafLeft M |>.map` with source and target spelled through
  `tensorSheafRight`, which is what makes `(g₁ ⊗ 𝟙) ≫ (𝟙 ⊗ g₂)` a type-correct composite;
* `freeTensorFreeIsoRight` is `Stacks.SheafOfModules.freeTensorFreeIso` at the same spelling.

Every statement in `Stacks.SheafOfModules.presentationTensorSheaf` is written through these, and
the crossings happen only where a term is *supplied*, by `:=` or `exact`, where definitional
equality is checked once.

**Zero-morphism preservation.** `CategoryTheory.Limits.isColimitCoforkMapOfIsColimit'` needs
`CategoryTheory.Functor.PreservesZeroMorphisms` of the functor it transports a cokernel along.
For the sheafification and the forgetful functor this holds because both are adjoints; for the
objectwise tensor product it is `PresheafOfModules.tensorRight_map_zero`. The composite instance
is assembled by hand rather than by `infer_instance` after an `unfold`, because the unfolded form
mentions `Stacks.commRingSheafToRingSheaf 𝒪♯` and unifying that with
`?𝒪 ⋙ forget₂ CommRingCat RingCat` is a higher-order problem instance search does not solve.

**Universes and generality.** The site universes `u`, `v` are independent of the module universe
`w`, which is also the ring universe, as `Stacks.SheafOfModules.Tensor.sheafTensor` requires
(see `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras`). The
results about presentations of tensor products hold over an arbitrary site; only the final
conclusion is stated on a ringed space, because that is where Tag 01CL reads quasi-coherence and
because `HasBinaryProducts` of the site, which the coproduct builder
`SheafOfModules.QuasicoherentData.coprodOfSmall` uses, is then automatic.

## References

* [Stacks Project, Lemma 17.21.5 (Tag 01CL)](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Lemma 17.16.4 (Tag 01CE)](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Lemma 17.21.3 (Tag 01CJ)](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.Sheaf

open scoped TensorProduct

universe v u w

namespace CategoryTheory

section Prod

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- In a product of two categories, a morphism of the first factor and a morphism of the second
commute when each is tensored with an identity. -/
lemma prod_id_comp_comp_id {A A' : C} {B B' : D} (a : A ⟶ A') (b : B ⟶ B') :
    (show (A, B) ⟶ (A, B') from (𝟙 A, b)) ≫ (show (A, B') ⟶ (A', B') from (a, 𝟙 B')) =
      (show (A, B) ⟶ (A', B) from (a, 𝟙 B)) ≫ (show (A', B) ⟶ (A', B') from (𝟙 A', b)) := by
  simp

/-- Composing two morphisms of the second factor of a product of categories, with the first
component the identity. -/
lemma prod_id_comp_id_comp {A : C} {B B' B'' : D} (b : B ⟶ B') (b' : B' ⟶ B'') :
    (show (A, B) ⟶ (A, B') from (𝟙 A, b)) ≫ (show (A, B') ⟶ (A, B'') from (𝟙 A, b')) =
      (show (A, B) ⟶ (A, B'') from (𝟙 A, b ≫ b')) := by
  simp

end Prod

namespace Limits

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasBinaryCoproducts D]
  {A₁ A₂ B E G : D}

/-- **A cokernel of a morphism out of a binary coproduct, computed in two steps.** If `g` is a
cokernel of `u₁` and `h` is a cokernel of `u₂ ≫ g`, then `g ≫ h` is a cokernel of
`coprod.desc u₁ u₂`. -/
noncomputable def isCokernelCoprodDesc {u₁ : A₁ ⟶ B} {u₂ : A₂ ⟶ B} {g : B ⟶ E} {h : E ⟶ G}
    {w₁ : u₁ ≫ g = 0} (hg : IsColimit (CokernelCofork.ofπ g w₁))
    {w₂ : (u₂ ≫ g) ≫ h = 0} (hh : IsColimit (CokernelCofork.ofπ h w₂))
    (w : coprod.desc u₁ u₂ ≫ (g ≫ h) = 0) :
    IsColimit (CokernelCofork.ofπ (g ≫ h) w) := by
  have hι₁ : ∀ s : CokernelCofork (coprod.desc u₁ u₂), u₁ ≫ Cofork.π s = 0 := fun s =>
    calc u₁ ≫ Cofork.π s
        = coprod.inl ≫ coprod.desc u₁ u₂ ≫ Cofork.π s := by rw [coprod.inl_desc_assoc]
      _ = 0 := by rw [CokernelCofork.condition, comp_zero]
  have hι₂ : ∀ s : CokernelCofork (coprod.desc u₁ u₂), u₂ ≫ Cofork.π s = 0 := fun s =>
    calc u₂ ≫ Cofork.π s
        = coprod.inr ≫ coprod.desc u₁ u₂ ≫ Cofork.π s := by rw [coprod.inr_desc_assoc]
      _ = 0 := by rw [CokernelCofork.condition, comp_zero]
  have hgd : ∀ {W : D} (k : B ⟶ W) (hk : u₁ ≫ k = 0),
      g ≫ hg.desc (CokernelCofork.ofπ k hk) = k := fun _ _ => Cofork.IsColimit.π_desc hg
  have hge : ∀ {W : D} (k l : E ⟶ W), g ≫ k = g ≫ l → k = l := fun _ _ e =>
    Cofork.IsColimit.hom_ext hg e
  have hhd : ∀ {W : D} (k : E ⟶ W) (hk : (u₂ ≫ g) ≫ k = 0),
      h ≫ hh.desc (CokernelCofork.ofπ k hk) = k := fun _ _ => Cofork.IsColimit.π_desc hh
  have hhe : ∀ {W : D} (k l : G ⟶ W), h ≫ k = h ≫ l → k = l := fun _ _ e =>
    Cofork.IsColimit.hom_ext hh e
  have hcond : ∀ s : CokernelCofork (coprod.desc u₁ u₂),
      (u₂ ≫ g) ≫ hg.desc (CokernelCofork.ofπ (Cofork.π s) (hι₁ s)) = 0 := fun s => by
    rw [Category.assoc, hgd _ (hι₁ s), hι₂ s]
  refine Cofork.IsColimit.mk _ (fun s => hh.desc (CokernelCofork.ofπ _ (hcond s)))
    (fun s => ?_) (fun s m hm => ?_)
  · rw [Cofork.π_ofπ, Category.assoc, hhd _ (hcond s), hgd _ (hι₁ s)]
  · rw [Cofork.π_ofπ, Category.assoc] at hm
    refine hhe m _ ?_
    rw [hhd _ (hcond s)]
    exact hge (h ≫ m) _ (by rw [hgd _ (hι₁ s)]; exact hm)

end Limits

end CategoryTheory

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Naturality of the symmetry of the objectwise tensor product of presheaves of modules, in
both variables at once.** `Stacks.tensorCommHom_comp_tensorRight_map` is the special case in which
the first morphism is an identity. -/
lemma tensorHom_tensorCommHom
    {F F' G G' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    (u : F ⟶ F') (v : G ⟶ G') :
    tensorHom u v ≫ Stacks.tensorCommHom F' G' =
      Stacks.tensorCommHom F G ≫ tensorHom v u :=
  tensorObj_hom_ext fun X x y ↦ by
    refine Eq.trans ?_ (tensorHom_tmul v u X y x).symm
    exact congrArg (fun z ↦ Hom.app (Stacks.tensorCommHom F' G') X z)
      (tensorHom_tmul u v X x y)

/-- Tensoring presheaves of modules on the right sends the zero morphism to the zero morphism. -/
lemma tensorRight_map_zero (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))
    (A B : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) :
    (Stacks.tensorRight (O := O) F).map (0 : A ⟶ B) = 0 := by
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  simp

/-- Tensoring presheaves of modules on the right by a fixed presheaf preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorRight
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)) :
    Functor.PreservesZeroMorphisms
      (show PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat) ⥤
          PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat) from
        Stacks.tensorRight (O := O) F) where
  map_zero A B := tensorRight_map_zero F A B

end PresheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-! ### The two variables of the tensor product, as endofunctors at one spelling -/

/-- Sheafification of presheaves of modules in the spelling
`Stacks.SheafOfModules.Tensor.sheafTensor` uses. -/
noncomputable abbrev moduleSheafifyToRingCat :
    PresheafOfModules.{w} (Osharp.obj ⋙ forget₂ CommRingCat RingCat) ⥤
      _root_.SheafOfModules.{w} (toRingCat J Osharp) :=
  PresheafOfModules.sheafification (R := toRingCat J Osharp) (𝟙 (toRingCat J Osharp).obj)

/-- **Tensoring on the right by a fixed sheaf of modules**, as an endofunctor of
`SheafOfModules (CategoryTheory.Sheaf.toRingCat J O♯)`. This is `Stacks.sheafTensorRight`, whose
source and target are spelled over `Stacks.commRingSheafToRingSheaf O♯`; the retyping is a `def`
with an ascribed type, not an `abbrev`, because the two spellings are different
discrimination-tree keys and a reducible wrapper would reintroduce both. -/
noncomputable def tensorSheafRight (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    _root_.SheafOfModules.{w} (toRingCat J Osharp) ⥤
      _root_.SheafOfModules.{w} (toRingCat J Osharp) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).flip.obj M)

/-- `Stacks.SheafOfModules.tensorSheafRight` is the first variable of the tensor bifunctor. -/
theorem tensorSheafRight_obj (M A : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    (tensorSheafRight J M).obj A =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A).obj M := rfl

/-- `Stacks.SheafOfModules.tensorSheafRight` on morphisms. -/
theorem tensorSheafRight_map (M : _root_.SheafOfModules.{w} (toRingCat J Osharp))
    {A A' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (f : A ⟶ A') :
    (tensorSheafRight J M).map f =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map f).app M := rfl

/-- Tensoring sheaves of modules on the right by a fixed sheaf preserves finite colimits. -/
noncomputable instance preservesFiniteColimits_tensorSheafRight
    (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    PreservesFiniteColimits (tensorSheafRight J M) :=
  Stacks.preservesFiniteColimits_sheafTensorRight Osharp M

/-- Tensoring sheaves of modules on the right sends the zero morphism to the zero morphism: it is
the composite of the forgetful functor, the objectwise tensor product and sheafification, and the
middle factor is where the content sits. -/
noncomputable instance preservesZeroMorphisms_tensorSheafRight
    (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    Functor.PreservesZeroMorphisms (tensorSheafRight J M) where
  map_zero A B :=
    (congrArg (moduleSheafifyToRingCat J).map
      (PresheafOfModules.tensorRight_map_zero M.val A.val B.val)).trans
      (Functor.map_zero _ _ _)

/-- **Tensoring on the left by a fixed sheaf of modules**, as an endofunctor. This is the second
variable of `Stacks.SheafOfModules.Tensor.sheafTensor`;
`Stacks.SheafOfModules.tensorSheafRight` is the first. -/
noncomputable def tensorSheafLeft (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    _root_.SheafOfModules.{w} (toRingCat J Osharp) ⥤
      _root_.SheafOfModules.{w} (toRingCat J Osharp) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M

/-! ### The symmetry of the tensor product of sheaves of modules -/

/-- **The symmetry of the tensor product of sheaves of modules**: the sheafification of the
symmetry of the objectwise tensor product. -/
noncomputable def tensorSheafCommIso
    (M N : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    (tensorSheafLeft J M).obj N ≅ (tensorSheafRight J M).obj N :=
  (moduleSheafifyToRingCat J).mapIso (Stacks.tensorObjComm M.val N.val)

/-- Naturality of `Stacks.SheafOfModules.tensorSheafCommIso`: it exchanges the two variables of
the tensor product. -/
lemma tensorSheafLeft_map_comp_tensorSheafCommIso
    (M : _root_.SheafOfModules.{w} (toRingCat J Osharp))
    {N N' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (g : N ⟶ N') :
    (tensorSheafLeft J M).map g ≫ (tensorSheafCommIso J M N').hom =
      (tensorSheafCommIso J M N).hom ≫ (tensorSheafRight J M).map g :=
  ((moduleSheafifyToRingCat J).map_comp _ _).symm.trans
    ((congrArg (moduleSheafifyToRingCat J).map
      (PresheafOfModules.tensorHom_tensorCommHom (𝟙 M.val) g.val)).trans
      ((moduleSheafifyToRingCat J).map_comp _ _))

/-- Tensoring on the left is naturally isomorphic to tensoring on the right, by the symmetry. -/
noncomputable def tensorSheafLeftIso (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    tensorSheafLeft J M ≅ tensorSheafRight J M :=
  NatIso.ofComponents (fun N => tensorSheafCommIso J M N)
    fun g => tensorSheafLeft_map_comp_tensorSheafCommIso J M g

/-- Tensoring sheaves of modules on the left by a fixed sheaf preserves zero morphisms, through
the symmetry `Stacks.SheafOfModules.tensorSheafLeftIso`. -/
noncomputable instance preservesZeroMorphisms_tensorSheafLeft
    (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    Functor.PreservesZeroMorphisms (tensorSheafLeft J M) :=
  Functor.preservesZeroMorphisms_of_iso (tensorSheafLeftIso J M).symm

/-- Tensoring sheaves of modules on the left by a fixed sheaf preserves finite colimits, through
the symmetry `Stacks.SheafOfModules.tensorSheafLeftIso`. -/
noncomputable instance preservesFiniteColimits_tensorSheafLeft
    (M : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    PreservesFiniteColimits (tensorSheafLeft J M) :=
  preservesFiniteColimits_of_natIso (tensorSheafLeftIso J M).symm

/-- **Bifunctoriality of the tensor product of sheaves of modules**: tensoring in the first
variable and in the second commute. -/
lemma tensorSheafLeft_map_comp_tensorSheafRight_map
    {A A' B B' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (a : A ⟶ A') (b : B ⟶ B') :
    (tensorSheafLeft J A).map b ≫ (tensorSheafRight J B').map a =
      (tensorSheafRight J B).map a ≫ (tensorSheafLeft J A').map b :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map a).naturality b

/-! ### One spelling for the two variables -/

open _root_.SheafOfModules in
/-- **Tensoring a morphism on the left by `M`**, with source and target spelled through
`Stacks.SheafOfModules.tensorSheafRight`. The two spellings `(A ⊗ B)` of the tensor product
coming from the two variables are definitionally equal, but `CategoryStruct.comp` stores one of
them, so a composite mixing them is not type-correct at `implicit` transparency and no rewrite
may cross it. Every statement in the proof below is written through this one spelling. -/
noncomputable def tensorSheafRightMapLeft (M : _root_.SheafOfModules.{w} (toRingCat J Osharp))
    {B B' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (g : B ⟶ B') :
    (tensorSheafRight J B).obj M ⟶ (tensorSheafRight J B').obj M :=
  (tensorSheafLeft J M).map g

open _root_.SheafOfModules in
/-- `Stacks.SheafOfModules.freeTensorFreeIso` at the spelling of
`Stacks.SheafOfModules.tensorSheafRight`. -/
noncomputable def freeTensorFreeIsoRight (I K : Type w) :
    (tensorSheafRight J (free (R := toRingCat J Osharp) K)).obj
        (free (R := toRingCat J Osharp) I) ≅ free (R := toRingCat J Osharp) (I × K) :=
  freeTensorFreeIso J I K

/-- `Stacks.SheafOfModules.tensorSheafRightMapLeft` is functorial. -/
lemma tensorSheafRightMapLeft_comp (M : _root_.SheafOfModules.{w} (toRingCat J Osharp))
    {B B' B'' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (g : B ⟶ B') (g' : B' ⟶ B'') :
    tensorSheafRightMapLeft J M g ≫ tensorSheafRightMapLeft J M g' =
      tensorSheafRightMapLeft J M (g ≫ g') :=
  ((tensorSheafLeft J M).map_comp g g').symm

/-- `Stacks.SheafOfModules.tensorSheafRightMapLeft` of the zero morphism is zero. -/
lemma tensorSheafRightMapLeft_zero (M B B' : _root_.SheafOfModules.{w} (toRingCat J Osharp)) :
    tensorSheafRightMapLeft J M (0 : B ⟶ B') = 0 :=
  Functor.map_zero (tensorSheafLeft J M) B B'

open _root_.SheafOfModules in
/-- Bifunctoriality, at the pinned spelling. -/
lemma tensorSheafRightMapLeft_comp_tensorSheafRight_map
    {A A' B B' : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (a : A ⟶ A') (b : B ⟶ B') :
    tensorSheafRightMapLeft J A b ≫ (tensorSheafRight J B').map a =
      (tensorSheafRight J B).map a ≫ tensorSheafRightMapLeft J A' b :=
  tensorSheafLeft_map_comp_tensorSheafRight_map J a b

/-! ### The tensor product of two presented sheaves of modules -/

open _root_.SheafOfModules in
/-- **The tensor product of two sheaves of modules presented by free sheaves of modules is itself
presented by free sheaves of modules**, with generators `σ₁ × σ₂` and relations
`(ι₁ × σ₂) ⊕ (σ₁ × ι₂)`. This is the key step of Stacks 01CE: the tensor product of the two
exact sequences `free ι₁ ⟶ free σ₁ ⟶ M ⟶ 0` and `free ι₂ ⟶ free σ₂ ⟶ N ⟶ 0` is the exact
sequence
`(free ι₁ ⊗ free σ₂) ⊕ (free σ₁ ⊗ free ι₂) ⟶ free σ₁ ⊗ free σ₂ ⟶ M ⊗ N ⟶ 0`. -/
noncomputable def presentationTensorSheaf {ι₁ σ₁ ι₂ σ₂ : Type w}
    {M N : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    {f₁ : free (R := toRingCat J Osharp) ι₁ ⟶ free σ₁} {g₁ : free σ₁ ⟶ M}
    {w₁ : f₁ ≫ g₁ = 0} (h₁ : IsColimit (CokernelCofork.ofπ g₁ w₁))
    {f₂ : free (R := toRingCat J Osharp) ι₂ ⟶ free σ₂} {g₂ : free σ₂ ⟶ N}
    {w₂ : f₂ ≫ g₂ = 0} (h₂ : IsColimit (CokernelCofork.ofπ g₂ w₂)) :
    ((tensorSheafRight J N).obj M).Presentation := by
  have hsq := tensorSheafRightMapLeft_comp_tensorSheafRight_map J g₁ f₂
  have e₁ := isColimitCoforkMapOfIsColimit'
    (tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)) w₁ h₁
  have e₁' := isColimitCoforkMapOfIsColimit'
    (tensorSheafRight J (free (R := toRingCat J Osharp) ι₂)) w₁ h₁
  have hepi : Epi ((tensorSheafRight J (free (R := toRingCat J Osharp) ι₂)).map g₁) :=
    epi_of_isColimit_cofork e₁'
  have e₂ : IsColimit (CokernelCofork.ofπ (tensorSheafRightMapLeft J M g₂)
      (show tensorSheafRightMapLeft J M f₂ ≫ tensorSheafRightMapLeft J M g₂ = 0 from by
        rw [tensorSheafRightMapLeft_comp, w₂, tensorSheafRightMapLeft_zero])) :=
    isColimitCoforkMapOfIsColimit' (tensorSheafLeft J M) w₂ h₂
  have e₃ := isCokernelEpiComp (hg := hepi) e₂
    ((tensorSheafRight J (free (R := toRingCat J Osharp) ι₂)).map g₁) hsq
  have h₁₀ : (tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map f₁ ≫
      ((tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map g₁ ≫
        tensorSheafRightMapLeft J M g₂) = 0 := by
    rw [← Category.assoc, ← Functor.map_comp, w₁, Functor.map_zero, zero_comp]
  have h₂₀ : tensorSheafRightMapLeft J (free (R := toRingCat J Osharp) σ₁) f₂ ≫
      ((tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map g₁ ≫
        tensorSheafRightMapLeft J M g₂) = 0 := by
    rw [← Category.assoc, hsq, Category.assoc, tensorSheafRightMapLeft_comp, w₂,
      tensorSheafRightMapLeft_zero, comp_zero]
  have hzero : coprod.desc
        ((tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map f₁)
        (tensorSheafRightMapLeft J (free (R := toRingCat J Osharp) σ₁) f₂) ≫
      ((tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map g₁ ≫
        tensorSheafRightMapLeft J M g₂) = 0 := by
    refine coprod.hom_ext ?_ ?_
    · rw [comp_zero, coprod.inl_desc_assoc]
      exact h₁₀
    · rw [comp_zero, coprod.inr_desc_assoc]
      exact h₂₀
  have e₄ := isCokernelCoprodDesc e₁ e₃ hzero
  refine presentationOfIsCokernelFree
    ((coprod.mapIso (freeTensorFreeIsoRight J ι₁ σ₂) (freeTensorFreeIsoRight J σ₁ ι₂) ≪≫
        freeSumIso (R := toRingCat J Osharp) (ι₁ × σ₂) (σ₁ × ι₂)).inv ≫
      coprod.desc
        ((tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map f₁)
        (tensorSheafRightMapLeft J (free (R := toRingCat J Osharp) σ₁) f₂) ≫
      (freeTensorFreeIsoRight J σ₁ σ₂).hom)
    ((freeTensorFreeIsoRight J σ₁ σ₂).inv ≫
      (tensorSheafRight J (free (R := toRingCat J Osharp) σ₂)).map g₁ ≫
      tensorSheafRightMapLeft J M g₂) ?_ ?_
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, hzero, comp_zero]
  · exact IsCokernel.ofIso _ e₄ _
      (coprod.mapIso (freeTensorFreeIsoRight J ι₁ σ₂) (freeTensorFreeIsoRight J σ₁ ι₂) ≪≫
        freeSumIso (R := toRingCat J Osharp) (ι₁ × σ₂) (σ₁ × ι₂))
      (freeTensorFreeIsoRight J σ₁ σ₂) (Iso.refl _) (by simp) (by simp)

/-- **The tensor product of two presented sheaves of modules is presented.** -/
theorem nonempty_presentation_tensorSheaf
    {M N : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    (p : M.Presentation) (q : N.Presentation) :
    Nonempty ((tensorSheafRight J N).obj M).Presentation :=
  ⟨presentationTensorSheaf J p.isColimitRelationsHom q.isColimitRelationsHom⟩

/-! ### Every tensor power of a presented sheaf of modules is presented -/

open _root_.SheafOfModules in
/-- **From a presentation of `F`, every tensor power of `F` has a presentation.** This is the
tensor-algebra analogue of `Stacks.SheafOfModules.nonempty_presentation_symmetricPower`, and
unlike it the argument is an induction on the degree rather than an appeal to Tag 01CJ: the
degree-`n+2` tensor power is `F ⊗ Tⁿ⁺¹(F)` by definition, so
`Stacks.SheafOfModules.nonempty_presentation_tensorSheaf` applies. -/
theorem nonempty_presentation_tensorPower
    {F : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (p : F.Presentation) (n : ℕ) :
    Nonempty (_root_.SheafOfModules.tensorPower J F n).Presentation := by
  induction n with
  | zero => exact ⟨presentationUnit⟩
  | succ m ih =>
    match m, ih with
    | 0, _ => exact ⟨p⟩
    | (m + 1), ih =>
      obtain ⟨q⟩ := ih
      exact nonempty_presentation_tensorSheaf J p q

/-! ### The same over an object of the site -/

section Over

variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

open _root_.SheafOfModules in
/-- **A presentation of `F` over an object `U` of the site presents every tensor power of `F`
over that same `U`.** The uniformity in the degree — one object of the site presenting every
degree — is the content of Stacks 01CL for the tensor algebra, and this is where it is
established: the object is the one over which `F` is presented, and no further shrinking happens
in any degree. -/
theorem nonempty_presentation_tensorPower_over (U : C)
    {F : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (p : (F.over U).Presentation) (n : ℕ) :
    Nonempty ((_root_.SheafOfModules.tensorPower J F n).over U).Presentation := by
  induction n with
  | zero => exact ⟨presentationUnit⟩
  | succ m ih =>
    match m, ih with
    | 0, _ => exact ⟨p⟩
    | (m + 1), ih =>
      obtain ⟨q⟩ := ih
      obtain ⟨r⟩ := nonempty_presentation_tensorSheaf (J.over U) (Osharp := Osharp.over U) p q
      exact ⟨presentationOfIso
        (Stacks.TensorCoherence.tensorSheafOverIso F
          (_root_.SheafOfModules.tensorPower J F (m + 1)) U) r⟩

end Over

/-! ### Tag 01CK and Tag 01CL for the tensor powers -/

section Conclusion

universe t

/-- A presentation of `F` over an open presents every tensor piece of `A` over that open. -/
private theorem nonempty_presentation_tensor_piece_over {X : AlgebraicGeometry.RingedSpace.{t, t}}
    {F : _root_.SheafOfModules.{t} (structureSheafRing X)}
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (U : Opens X.carrier) (n : ℕ)
    (p : (F.over U).Presentation) :
    Nonempty ((A.tensor.piece (n : ℤ)).over U).Presentation :=
  ⟨presentationOfIso
    ((_root_.SheafOfModules.overFunctor (structureSheafRing X) U).mapIso
      (A.tensorPieceIso n)).symm
    (nonempty_presentation_tensorPower_over (Opens.grothendieckTopology X.carrier)
      (Osharp := X.sheaf) U p n).some⟩

open _root_.SheafOfModules in
/-- **Each tensor power of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** This is clause (5) of Stacks Tag 01CK for the tensor powers. A presentation of
`F` over an open presents `Tⁿ(F)` over that same open, by
`Stacks.SheafOfModules.nonempty_presentation_tensorPower_over`, so the covering family which
presents `F` presents each tensor power too. -/
@[stacks 01CK "tensor powers of a quasi-coherent module"]
theorem isQuasicoherent_tensorPower {X : AlgebraicGeometry.RingedSpace.{t, t}}
    (F : _root_.SheafOfModules.{t} (structureSheafRing X)) [F.IsQuasicoherent]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) (n : ℕ) :
    (A.tensor.piece (n : ℤ)).IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  have q : _root_.SheafOfModules.QuasicoherentData.{t, t, t, t} (A.tensor.piece (n : ℤ)) :=
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i =>
        (nonempty_presentation_tensor_piece_over A (c.X i) n (c.presentation i)).some }
  exact q.isQuasicoherent

open _root_.SheafOfModules in
/-- **The tensor algebra of a quasi-coherent sheaf of modules on a ringed space is
quasi-coherent.** This is the tensor assertion of Stacks Tag 01CL. The covering family is the one
that presents `F`; no degree needs a smaller open, because
`Stacks.SheafOfModules.nonempty_presentation_tensorPower_over` presents every degree over that
same open. -/
@[stacks 01CL "the tensor algebra of a quasi-coherent module sheaf is quasi-coherent"]
theorem isQuasicoherent_tensorAlgebraSheaf_of_isQuasicoherent
    {X : AlgebraicGeometry.RingedSpace.{t, t}}
    (F : _root_.SheafOfModules.{t} (structureSheafRing X)) [F.IsQuasicoherent]
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) F) :
    A.tensorAlgebraSheaf.IsQuasicoherent := by
  obtain ⟨c⟩ := _root_.SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := F)
  refine A.isQuasicoherent_tensorAlgebraSheaf c.X c.coversTop fun i n => ?_
  exact (nonempty_presentation_tensor_piece_over A (c.X i) n (c.presentation i)).some

end Conclusion

end Stacks.SheafOfModules

end
