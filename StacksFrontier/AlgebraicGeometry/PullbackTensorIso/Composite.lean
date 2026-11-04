module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# Tag 01CD along a composite, on global sections

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and let `A`, `B` be modules on `Z`. The
comparison of [Stacks, Tag 01CD] turns the pullback of a global section of `A ⊗ B` into a global
section of `f^*A ⊗ f^*B`; this file records that the operation is compatible with composition of
morphisms, which is what writing an equation in the fibre coordinates of a line bundle on a
*closed subscheme of a fibre product* needs: there the equation lives on the fibre product and
the section it is compared with is pulled back along the composite.

Two halves are needed, and only one of them was available. The half about sections,
`AlgebraicGeometry.pullbackGlobalSections_comp`, is stated for Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. The half about the tensor comparison,
`Stacks.PullbackTensorComposition.comparison_comp`, is stated for
`Stacks.DerivedPullback.Composition.modulePullbackComp` — a *different* contraction of the
iterated pullback, built by `CategoryTheory.Adjunction.leftAdjointCompIso` from the contraction
of the iterated pushforward, and no bridge between the two spellings is proved anywhere. Rather
than build that bridge, both halves are produced here at the second spelling: the section half
is `Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit` read at the top
open, and the tensor half is `comparison_comp` read on a global section.

## Main definitions

* `Stacks.PullbackTensorIso.pullbackCompHom`: the contraction `f^*g^*M ⟶ (f ≫ g)^*M` of an
  iterated pullback, at the spelling Tag 01CD's composition law is stated at.
* `Stacks.PullbackTensorIso.pullbackTensorSection`: **the pullback of a global section of a
  tensor product, read in the tensor product of the pullbacks** through Tag 01CD.

## Main results

* `Stacks.PullbackTensorIso.pullbackCompHom_pullbackGlobalSections`: the composition law for the
  pullback map on global sections, at that spelling.
* `Stacks.PullbackTensorIso.pullbackTensorSection_comp`: **Tag 01CD is compatible with the
  composition law for pullback**, read on a global section.
* `Stacks.PullbackTensorIso.tensorSheafMap_tensorSectionsAt`: the tensor product of two morphisms
  of modules, read on a product of two global sections.

## Implementation notes

The statements are at the scheme-level spellings of the pullback functor and of the tensor
product, and the inputs at the ringed-space ones. Crossing the two at the level of *morphisms*
does not elaborate inside the heartbeat budget — the comparison along a composite is a term with
three pullback functors and two sheafifications in it, and deciding the definitional equality of
the two spellings of each is what the cost consists of. Crossing them on a *section* is cheap,
and that is what is done below: `Stacks.PullbackTensorComposition.comparison_comp` is read on one
element by `congrArg`, and the composites on both sides are split by the definitional unfolding
that `Eq.trans` performs on the terms it joins.

For the same reason the proof does not rewrite with the two auxiliary identities. The types
`Γ(M, ⊤)` and `M.val.obj (op ⊤)` are definitionally equal and pairwise distinct as terms, so a
rewrite whose motive abstracts over a section of a tensor product is not type-correct at the
transparency `rw` builds its motive at; `congrArg`, whose type is checked at default
transparency, is used instead. This is the device
`StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections` already uses for the same reason.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.SheafOfModules (tensorSectionsAt)
open Stacks.RingedSpace (pullbackUnit)
open Stacks.DerivedPullback.Composition (modulePullbackComp)

universe u

@[expose] public noncomputable section

namespace Stacks.PullbackTensorIso

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The contraction `f^*g^*M ⟶ (f ≫ g)^*M` of an iterated pullback, at the spelling the
composition law for the comparison of [Stacks, Tag 01CD] is stated at. -/
abbrev pullbackCompHom (M : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶
      (Scheme.Modules.pullback (f ≫ g)).obj M :=
  (modulePullbackComp f.toLRSHom.toShHom g.toLRSHom.toShHom).hom.app M

/-- **The pullback of a global section of a tensor product, read in the tensor product of the
pullbacks** through the comparison of [Stacks, Tag 01CD]. -/
def pullbackTensorSection (A B : Y.Modules)
    (w : Γ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
        (Y.ringCatSheaf.property)⟩).obj (A)).obj (B)), ⊤)) :
    Γ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _
        (X.sheaf.obj) (forget₂ CommRingCat RingCat) (X.ringCatSheaf.property)⟩).obj
        (((Scheme.Modules.pullback f).obj A))).obj (((Scheme.Modules.pullback f).obj B))), ⊤) :=
  PresheafOfModules.Hom.app
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B).hom.val (op ⊤)
    (pullbackGlobalSections f ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
        (Y.ringCatSheaf.property)⟩).obj (A)).obj (B))) w)

/-- The pullback map on global sections is the unit of the pullback--pushforward adjunction at
the top open, at the ringed-space spelling the composition law is stated at. -/
private theorem pullbackGlobalSections_eq_pullbackUnit {W V : Scheme.{u}} (h : W ⟶ V)
    (N : V.Modules) (x : Γ(N, ⊤)) :
    pullbackGlobalSections h N x = pullbackUnit h.toLRSHom.toShHom N (op ⊤) x :=
  congrArg (fun φ : Γ(N, ⊤) ⟶ Γ((Scheme.Modules.pullback h).obj N, ⊤) => φ x)
    (pullbackGlobalSections_eq_unit h N)

/-- **The composition law for the pullback map on global sections**, at the spelling of the
contraction of an iterated pullback that Tag 01CD's composition law is stated at. -/
theorem pullbackCompHom_pullbackGlobalSections (M : Z.Modules) (s : Γ(M, ⊤)) :
    PresheafOfModules.Hom.app (pullbackCompHom f g M).val (op ⊤)
        (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj M)
          (pullbackGlobalSections g M s)) =
      pullbackGlobalSections (f ≫ g) M s := by
  rw [pullbackGlobalSections_eq_pullbackUnit, pullbackGlobalSections_eq_pullbackUnit,
    pullbackGlobalSections_eq_pullbackUnit]
  exact Stacks.PullbackTensorComposition.modulePullbackComp_hom_app_pullbackUnit
    f.toLRSHom.toShHom g.toLRSHom.toShHom M (op ⊤) s

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the composition law for pullback**,
read on a global section: the pullback of a global section of `A ⊗ B` along `f ≫ g`, read in
`(f ≫ g)^*A ⊗ (f ≫ g)^*B`, is its pullback along `g` and then along `f`, read in
`f^*g^*A ⊗ f^*g^*B` and carried along the contraction in each tensor factor. -/
theorem pullbackTensorSection_comp (A B : Z.Modules)
    (w : Γ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
        (Z.ringCatSheaf.property)⟩).obj (A)).obj (B)), ⊤)) :
    pullbackTensorSection (f ≫ g) A B w =
      PresheafOfModules.Hom.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
            ((pullbackCompHom f g A, pullbackCompHom f g B) :
              (((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj A),
                (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj B)) : _ × _) ⟶
                ((Scheme.Modules.pullback (f ≫ g)).obj A,
                  (Scheme.Modules.pullback (f ≫ g)).obj B))).val (op ⊤)
        (pullbackTensorSection f ((Scheme.Modules.pullback g).obj A)
          ((Scheme.Modules.pullback g).obj B) (pullbackTensorSection g A B w)) := by
  have hnat : ∀ x, PresheafOfModules.Hom.app
      ((Scheme.Modules.pullback f).map
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g A B).hom).val (op ⊤)
        (pullbackGlobalSections f
          ((Scheme.Modules.pullback g).obj
            ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
                Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
                (Z.ringCatSheaf.property)⟩).obj (A)).obj (B)))) x) =
      pullbackGlobalSections f
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat)
            (Y.ringCatSheaf.property)⟩).obj (((Scheme.Modules.pullback g).obj A))).obj
            (((Scheme.Modules.pullback g).obj B)))) (PresheafOfModules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g A B).hom.val (op ⊤) x) :=
    fun x => (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality f
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g A B).hom x).symm
  rw [pullbackTensorSection, pullbackTensorSection, pullbackTensorSection, ← hnat]
  exact (congrArg (fun z => PresheafOfModules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (f ≫ g) A B).hom.val (op ⊤) z)
      (pullbackCompHom_pullbackGlobalSections f g
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
            (Z.ringCatSheaf.property)⟩).obj (A)).obj (B))) w).symm).trans
    (congrArg (fun φ : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
              (Z.ringCatSheaf.property)⟩).obj (A)).obj (B)))) ⟶
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _ (X.sheaf.obj) (forget₂ CommRingCat RingCat)
              (X.ringCatSheaf.property)⟩).obj (((Scheme.Modules.pullback (f ≫ g)).obj A))).obj
              (((Scheme.Modules.pullback (f ≫ g)).obj B))) =>
        PresheafOfModules.Hom.app (SheafOfModules.Hom.val φ) (op ⊤)
          (pullbackGlobalSections f
            ((Scheme.Modules.pullback g).obj
              ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
                  Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
                  (Z.ringCatSheaf.property)⟩).obj (A)).obj (B))))
            (pullbackGlobalSections g
              ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.sheaf.obj,
                  Presheaf.isSheaf_of_isSheaf_comp _ (Z.sheaf.obj) (forget₂ CommRingCat RingCat)
                  (Z.ringCatSheaf.property)⟩).obj (A)).obj (B))) w)))
      (Stacks.PullbackTensorComposition.comparison_comp f.toLRSHom.toShHom
        g.toLRSHom.toShHom A B))

/-- The tensor product of two morphisms of modules, read on the product of two global sections:
it is the product of the two images. -/
theorem tensorSheafMap_tensorSectionsAt {W : Scheme.{u}} {A₁ A₂ B₁ B₂ : W.Modules}
    (u : A₁ ⟶ A₂) (v : B₁ ⟶ B₂) (a : Γ(A₁, ⊤)) (b : Γ(B₁, ⊤)) :
    PresheafOfModules.Hom.app
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩))).map
          ((u, v) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂))).val (op ⊤)
        (tensorSectionsAt W.sheaf.obj W.ringCatSheaf.property (op ⊤) A₁ B₁ a b) =
      tensorSectionsAt W.sheaf.obj W.ringCatSheaf.property (op ⊤) A₂ B₂
        (PresheafOfModules.Hom.app u.val (op ⊤) a)
        (PresheafOfModules.Hom.app v.val (op ⊤) b) :=
  Stacks.RingedSpace.tensorSheaf_map_unit_tmul W.toRingedSpace u v (op ⊤) a b

end Stacks.PullbackTensorIso

end
