module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace

/-!
# The canonical tensor map for the top higher direct image

Conclusion (b) of [Stacks, Tag 0EX3] reads

> `R^d f'_*(F' ⊗_{𝒪_{X'}} (f')^* G') = R^d f'_* F' ⊗_{𝒪_{Y'}} G'`

and the equality it asserts is not an equality of isomorphism classes: the two sheaves are
identified by the map that sends a local pure tensor `x ⊗ s` to the higher direct image of
`t ↦ t ⊗ (f')^* s`. This file states that canonicity condition, over schemes and with no
hypothesis beyond the morphism itself, and proves that it determines the map uniquely.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorLocalSection`: on an open `V`, the
  morphism `x ↦ x ⊗ s` from `F` restricted to `V` into the tensor sheaf of [Stacks, Tag 01CB]
  restricted to `V`, for a section `s` of `G` over `V`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.higherDirectImageTensorSection`: tensoring with
  a local section and then taking the `n`-th higher direct image, transported across the
  restriction comparison of [Stacks, Tag 01E5].
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.IsHigherDirectImageTensorMap`: the canonicity
  condition on a map `R^n f_* F ⊗ G ⟶ R^n f_*(F ⊗ f^* G)`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.hom_ext_of_tensorSection`: two morphisms out of
  a tensor sheaf that agree on the local pure tensors are equal.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.eq_of_isHigherDirectImageTensorMap`: **the
  canonicity condition determines the map.** At most one morphism satisfies it, so the data
  asserted by conclusion (b) is a property of the two sheaves and not a choice.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageTensorComparisonOfIsIso`: the
  remaining content of conclusion (b), stated exactly: a canonical map which is invertible
  supplies the isomorphism together with its characterisation.

## Implementation notes

**What is not here.** Conclusion (b) itself is not proved. Two inputs are missing, and both are
named precisely below.

*The map.* Building a canonical map out of `tensorSheaf` means, by the sheafification
adjunction, giving a bilinear family on sections — `PresheafOfModules.ofBilinear` and
`Stacks.BilinearMap` are the library interface for exactly that. Its naturality field is the
obligation that `higherDirectImageTensorSection` be compatible with shrinking the open: for
`W ⊆ V` the comparison built over `V` restricted to `W` must agree with the one built over `W`.
That is a statement about `Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso`,
namely its compatibility with a nested pair of opens, and the Tag 01E5 cluster
(`StacksDraft/Ch20/Sec14/Tag01E5*.lean`) does not contain it in any form: it has the
degree-zero normalisation and the characterisation on an injective resolution, and nothing about
two nested opens. Everything else in the construction is present.

*Invertibility.* The source argument is: reduce to `Y'` affine, where
`Stacks.Cohomology.AffineBase.cohomologyIsoGlobalSectionsRightDerivedPushforward`
([Stacks, Tag 01XK]) turns the higher direct image into cohomology; conclusion (a) in degree
`d + 1` makes `M ↦ H^d(X', F' ⊗ (f')^* M~)` right exact; [Stacks, Tag 01FF] makes it commute
with direct sums; `Stacks.EilenbergWatts.iso` — the step the source leaves to the reader, proved
in `EilenbergWatts.lean` — identifies it with tensoring by `H^d(X', F')`; and
`Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_higherDirectImage`
([Stacks, Tag 01XJ]) translates that back. Of those, only conclusion (a) is open, and it is open
only in the affine case:
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_affineCase`
carries the affine case as a hypothesis.

**Two spellings of the section ring.** A sheaf of modules on a scheme is a module over
`X.ringCatSheaf.obj.obj W` in `RingCat`, while the presheaf tensor product of
[Stacks, Tag 01CB] is formed over `X.presheaf.obj W` in `CommRingCat`. The two carriers and
their ring structures are definitionally equal and instance synthesis does not cross between
them, so `moduleOfPresheafRing` bridges them once as a local instance and every linear map below
is introduced with its ring spelled out. That is what makes the section-level maps elaborate;
no transparency option is used.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- The module structure of a sheaf of modules on a scheme, read over the `CommRingCat` spelling
`X.presheaf.obj W` of the section ring rather than the `RingCat` spelling
`X.ringCatSheaf.obj.obj W` it is declared over. The two are definitionally equal; instance
synthesis does not cross between them, and the presheaf tensor product of [Stacks, Tag 01CB] is
formed over the former. -/
@[instance_reducible]
def moduleOfPresheafRing {X : Scheme.{u}} (F : X.Modules)
    (W : (Opens X.carrier)ᵒᵖ) : Module ↑(X.presheaf.obj W) ↑(F.val.obj W) :=
  inferInstanceAs (Module ↑(X.ringCatSheaf.obj.obj W) ↑(F.val.obj W))

attribute [local instance] moduleOfPresheafRing

/-- The sheafification unit of the presheaf tensor product, on sections over `W`. -/
noncomputable def toTensorSheafLinear (X : Scheme.{u}) (F G : X.Modules)
    (W : (Opens X.carrier)ᵒᵖ) :
    let tensorSections : ModuleCat.{u} (X.presheaf.obj W) :=
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val.obj W
    ↑(((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F.val)
        (G.val))).obj W) →ₗ[↑(X.presheaf.obj W)]
      tensorSections :=
  ((sheafifyUnit X.toRingedSpace
    ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F.val) (G.val)))).app W).hom

/-- The map `x ↦ x ⊗ t` into the tensor sheaf, on sections over `W`. -/
noncomputable def tensorSectionLinear (X : Scheme.{u}) (F G : X.Modules)
    (W : (Opens X.carrier)ᵒᵖ) (t : G.val.obj W) :
    let tensorSections : ModuleCat.{u} (X.presheaf.obj W) :=
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G).val.obj W
    ↑(F.val.obj W) →ₗ[↑(X.presheaf.obj W)] tensorSections :=
  (toTensorSheafLinear X F G W).comp
    ((TensorProduct.mk (X.presheaf.obj W) (F.val.obj W) (G.val.obj W)).flip t)

/-- The component of `tensorLocalSection` over an open `W` of `V`. -/
noncomputable def tensorLocalSectionApp (X : Scheme.{u}) (F G : X.Modules)
    (V : X.Opens) (s : Γ(G, V)) (W : (Opens ↥V)ᵒᵖ) :
    (F.restrict V.ι).val.obj W ⟶
      (Scheme.Modules.restrict ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)))
        V.ι).val.obj W :=
  (ModuleCat.restrictScalars (V.ι.appIso W.unop).inv.hom).map
    (ModuleCat.ofHom (tensorSectionLinear X F G (op (V.ι ''ᵁ W.unop))
      (G.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)))

/-- **Tensoring with a local section.** On the open `V`, the morphism `x ↦ x ⊗ s` from `F`
restricted to `V` into the tensor sheaf of [Stacks, Tag 01CB] restricted to `V`, for a section
`s` of `G` over `V`. Naturality is the compatibility of the sheafification unit with restriction
together with the transitivity of restriction of `s`. -/
noncomputable def tensorLocalSection (X : Scheme.{u}) (F G : X.Modules)
    (V : X.Opens) (s : Γ(G, V)) :
    F.restrict V.ι ⟶ Scheme.Modules.restrict ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G))) V.ι where
  val :=
    { app := tensorLocalSectionApp X F G V s
      naturality := by
        intro W W' i
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        refine Eq.trans ?_ (PresheafOfModules.naturality_apply
          (sheafifyUnit X.toRingedSpace
            ((PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (F.val) (G.val))))
          ((V.ι.opensFunctor).op.map i)
          (x ⊗ₜ[X.presheaf.obj (op (V.ι ''ᵁ W.unop))]
            (G.presheaf.map (homOfLE (V.ι_image_le W.unop)).op s)))
        exact congrArg (fun y : G.val.obj (op (V.ι ''ᵁ W'.unop)) =>
          toTensorSheafSection X.toRingedSpace F G (op (V.ι ''ᵁ W'.unop))
            ((F.presheaf.map ((V.ι.opensFunctor).op.map i) x)
              ⊗ₜ[X.presheaf.obj (op (V.ι ''ᵁ W'.unop))] y))
          (ConcreteCategory.congr_hom (G.presheaf.map_comp (homOfLE (V.ι_image_le W.unop)).op
            ((V.ι.opensFunctor).op.map i)) s) }

/-- **The value of `tensorLocalSection` over the whole of `V`.** Composed with the restriction to
`V` of a morphism `c` out of the tensor sheaf, its component at the top open of `V` is `c` read
on the pure tensor `a ⊗ s`. -/
theorem tensorLocalSection_top {X : Scheme.{u}} {A G T : X.Modules} (V : X.Opens)
    (t : Γ(G, V)) (c : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (G)) ⟶ T)
    (a : (A.restrict V.ι).val.obj (op ⊤)) :
    ((tensorLocalSection X A G V t ≫ (Scheme.Modules.restrictFunctor V.ι).map c).val.app
        (op ⊤)).hom a =
      (c.val.app (op (V.ι ''ᵁ (⊤ : Opens ↥V)))).hom
        (toTensorSheafSection X.toRingedSpace A G (op (V.ι ''ᵁ (⊤ : Opens ↥V)))
          (a ⊗ₜ[X.presheaf.obj (op (V.ι ''ᵁ (⊤ : Opens ↥V)))]
            (G.presheaf.map (homOfLE (V.ι_image_le (⊤ : Opens ↥V))).op t))) := rfl

/-- A morphism out of a tensor sheaf, read on sections over `W` as a linear map out of the
tensor product of the two modules of sections. -/
noncomputable def tensorSheafHomLinear {X : Scheme.{u}} {A G T : X.Modules}
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (G)) ⟶ T)
    (W : (Opens X.carrier)ᵒᵖ) :
    TensorProduct ↑(X.presheaf.obj W) ↑(A.val.obj W) ↑(G.val.obj W) →ₗ[↑(X.presheaf.obj W)]
      ↑(T.val.obj W) :=
  let tensorSections : ModuleCat.{u} (X.presheaf.obj W) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj G).val.obj W
  (show tensorSections →ₗ[↑(X.presheaf.obj W)] ↑(T.val.obj W) from
    (c.val.app W).hom).comp (toTensorSheafLinear X A G W)

/-- **Local pure tensors determine a morphism out of a tensor sheaf.** The tensor sheaf is the
sheafification of the presheaf tensor product, so a morphism out of it is determined by its
composite with the sheafification unit (`PresheafOfModules.sheafification_hom_ext`), and that
composite is determined on sections by the pure tensors. -/
theorem hom_ext_of_tensorSection {X : Scheme.{u}} {A G T : X.Modules}
    {c₁ c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (G)) ⟶ T}
    (h : ∀ (W : (X.Opens)ᵒᵖ) (a : A.val.obj W) (t : G.val.obj W),
      (c₁.val.app W).hom (toTensorSheafSection X.toRingedSpace A G W
          (a ⊗ₜ[X.presheaf.obj W] t)) =
        (c₂.val.app W).hom (toTensorSheafSection X.toRingedSpace A G W
          (a ⊗ₜ[X.presheaf.obj W] t))) :
    c₁ = c₂ := by
  refine PresheafOfModules.sheafification_hom_ext ?_
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  have key : tensorSheafHomLinear c₁ W = tensorSheafHomLinear c₂ W :=
    TensorProduct.ext' fun a t => h W a t
  exact LinearMap.ext fun z => LinearMap.congr_fun key z

/-- Transport of a pure-tensor identity from the image `V.ι ''ᵁ ⊤` of the top open of `V` to `V`
itself. The two opens are equal but not definitionally so, and over `V` the restriction map of
the equality is the identity. -/
theorem transport_top {X : Scheme.{u}} {A G T : X.Modules}
    {c₁ c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (A)).obj (G)) ⟶ T}
    (U W : X.Opens) (hUW : W = U) (hle : W ≤ U)
    (HH : ∀ (t : Γ(G, U)) (a : A.val.obj (op W)),
      (c₁.val.app (op W)).hom (toTensorSheafSection X.toRingedSpace A G (op W)
          (a ⊗ₜ[X.presheaf.obj (op W)] (G.presheaf.map (homOfLE hle).op t))) =
        (c₂.val.app (op W)).hom (toTensorSheafSection X.toRingedSpace A G (op W)
          (a ⊗ₜ[X.presheaf.obj (op W)] (G.presheaf.map (homOfLE hle).op t)))) :
    ∀ (t : Γ(G, U)) (a : A.val.obj (op U)),
      (c₁.val.app (op U)).hom (toTensorSheafSection X.toRingedSpace A G (op U)
          (a ⊗ₜ[X.presheaf.obj (op U)] t)) =
        (c₂.val.app (op U)).hom (toTensorSheafSection X.toRingedSpace A G (op U)
          (a ⊗ₜ[X.presheaf.obj (op U)] t)) := by
  subst hUW
  intro t a
  have hid : (G.presheaf.map (homOfLE hle).op) t = t := by
    rw [show (homOfLE hle : W ⟶ W) = 𝟙 W from rfl, op_id, G.presheaf.map_id]
    rfl
  rw [← hid]
  exact HH t a

/-- **Tensoring with a local section and then taking the higher direct image.** For a section `s`
of `G` over `V`, the pullback adjunction unit turns `s` into a section of `f^* G` over
`f⁻¹(V)`, tensoring with it is a morphism over `f⁻¹(V)`, and the restriction comparison of
[Stacks, Tag 01E5] — the scheme-level
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso` — transports
its `n`-th higher direct image back to a morphism over `V`. -/
noncomputable def higherDirectImageTensorSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules)
    (n : ℕ) (V : Y.Opens) (s : Γ(G, V)) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F).restrict V.ι ⟶
      (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G))))).restrict V.ι :=
  (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V n F).inv ≫
    ((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (n : ℤ)).map
      (tensorLocalSection X F ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V s)) ≫
    (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f V n
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G))))).hom

/-- **The canonicity condition of [Stacks, Tag 0EX3] (b).** A map
`R^n f_* F ⊗ G ⟶ R^n f_*(F ⊗ f^* G)` is canonical when on every open it sends `x ⊗ s` to the
higher direct image of `t ↦ t ⊗ f^* s`. Local pure tensors generate the tensor sheaf, so this
fixes the map: see `eq_of_isHigherDirectImageTensorMap`. -/
def IsHigherDirectImageTensorMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G))))) : Prop :=
  ∀ (V : Y.Opens) (s : Γ(G, V)),
    tensorLocalSection Y
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F) G V s ≫
      (Scheme.Modules.restrictFunctor V.ι).map c =
        higherDirectImageTensorSection f F G n V s

/-- **The canonicity condition determines the map.** At most one morphism
`R^n f_* F ⊗ G ⟶ R^n f_*(F ⊗ f^* G)` satisfies `IsHigherDirectImageTensorMap`, so the
identification asserted by [Stacks, Tag 0EX3] (b) involves no choice. The condition is read at
the top open of each `V`, where it says exactly what the map does to the pure tensor `a ⊗ s`,
and `hom_ext_of_tensorSection` turns that into equality. -/
theorem eq_of_isHigherDirectImageTensorMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (G : Y.Modules) (n : ℕ)
    {c₁ c₂ : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G))))}
    (h₁ : IsHigherDirectImageTensorMap f F G n c₁)
    (h₂ : IsHigherDirectImageTensorMap f F G n c₂) :
    c₁ = c₂ := by
  refine hom_ext_of_tensorSection fun W a t => transport_top W.unop (W.unop.ι ''ᵁ ⊤)
    (Scheme.Opens.ι_image_top W.unop) (W.unop.ι_image_le ⊤) (fun t' a' => ?_) t a
  have hc := (h₁ W.unop t').trans (h₂ W.unop t').symm
  exact ((tensorLocalSection_top W.unop t' c₁ a').symm.trans (by rw [hc])).trans
    (tensorLocalSection_top W.unop t' c₂ a')

/-- **What remains of [Stacks, Tag 0EX3] (b), stated exactly.** A canonical map which is
invertible supplies the isomorphism of conclusion (b) together with the characterisation of its
inverse. Stated for an arbitrary morphism and arbitrary modules: the quasi-coherence hypotheses
and the top-degree vanishing of
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` are what the open half — invertibility —
needs, and nothing else in the conclusion uses them. -/
noncomputable def topDirectImageTensorComparisonOfIsIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (n : ℕ)
    (c : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
        ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G)))))
    (hc : IsHigherDirectImageTensorMap f F G n c) [IsIso c] :
    { e : ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Y.toRingedSpace)).presheaf, ((Y.toRingedSpace)).IsSheaf⟩).obj
          ((((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj F))).obj (G)) //
      IsHigherDirectImageTensorMap f F G n e.inv } :=
  ⟨(asIso c).symm, hc⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
