module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# The 2-Yoneda evaluation functor against the chosen pullbacks

Let `p : S ⥤ C` be fibred in groupoids and let `i : U ⟶ U'` be an arrow of `C`. The 2-Yoneda
lemma (`CategoryTheory.Functor.twoYonedaEvaluation_isEquivalence`, Stacks 004B) identifies a
functor over `C` on the slice `C/U'` with its value at the terminal object `(U', 𝟙 U')`, an
object of the fibre of `p` over `U'`. This file compares the *other* values of such a functor,
and the other components of a 2-morphism between two of them, with the chosen pullbacks supplied
by a prefibered structure on `p`.

The content is one isomorphism and one equation. The value of a functor over `C` at the object
`(U, i)` of `C/U'` and the chosen pullback along `i` of its value at the terminal object are two
cartesian lifts of `i`, hence canonically isomorphic in the fibre over `U`
(`CategoryTheory.Functor.TwoYoneda.pullbackFiberTwoYonedaIso`); and under that identification the
component at `(U, i)` of a 2-morphism is the morphism of chosen pullbacks induced by its
component at the terminal object
(`CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_app_eq_pullbackFiberHom`). So evaluation
determines a 2-morphism not only at the terminal object — which is faithfulness — but computably
at every object, in terms of `CategoryTheory.Functor.pullbackFiberHom`.

## Main definitions

* `CategoryTheory.Functor.TwoYoneda.sliceToTerminal`: the unique arrow `(U, i) ⟶ (U', 𝟙 U')` of
  the slice `C/U'`.
* `CategoryTheory.Functor.TwoYoneda.sliceObjFiber`: the value of a functor over `C` at `(U, i)`,
  as an object of the fibre of `p` over `U`.
* `CategoryTheory.Functor.TwoYoneda.pullbackFiberTwoYonedaIso`: the comparison of that value with
  the chosen pullback along `i` of the value at the terminal object.

## Main results

* `CategoryTheory.Functor.TwoYoneda.isCartesian_map_sliceToTerminal`: the image of
  `sliceToTerminal` is a cartesian lift of `i`.
* `CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_app_eq_pullbackFiberHom` and
  `CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_app_eq_comp`: the component at `(U, i)`
  of a 2-morphism, read through the comparison, in the bundled and in the factored form.
* `CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_preimage_app`: the component at the
  terminal object of the 2-morphism obtained from a morphism of fibre objects by fullness of
  evaluation is that morphism.

## Implementation notes

`CategoryTheory.BasedCategory.ofFunctor` and `CategoryTheory.Functor.Fiber` are semireducible, so
goals stated in terms of them are not type-correct at `implicit` transparency and the rewriting
tactics decline to act on them. The proofs below are therefore written as chains of `Eq.trans`
and `congrArg` rather than with `rw` or `simp only`, and the two cartesianness hypotheses of
`CategoryTheory.Functor.fiberIsoOfCartesian` are supplied by explicit terms rather than by
instance search. For the same reason the extensionality step uses
`CategoryTheory.Functor.fiber_hom_ext_of_cartesian`, which takes cartesianness as an argument and
reads the lifting conditions off the fibre's subtype, in place of
`CategoryTheory.Functor.IsStronglyCartesian.ext`, whose `IsHomLift` instance arguments are not
synthesizable here.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor.TwoYoneda

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]

/-- The unique arrow of the slice `C/U'` from the object `(U, i)` to the terminal object
`(U', 𝟙 U')`. -/
noncomputable def sliceToTerminal {U U' : C} (i : U ⟶ U') :
    (Over.mk i : Over U') ⟶ Over.mk (𝟙 U') :=
  Over.mkIdTerminal.from (Over.mk i)

/-- The value at the object `(U, i)` of the slice `C/U'` of a functor over `C` into `p`, as an
object of the fibre of `p` over `U`: the compatibility `G ⋙ p = Over.forget U'` says precisely
that it lies over `U`. -/
def sliceObjFiber (p : S ⥤ C) {U U' : C} (i : U ⟶ U')
    (G : BasedCategory.ofFunctor (Over.forget U') ⥤ᵇ BasedCategory.ofFunctor p) : p.Fiber U :=
  ⟨G.toFunctor.obj (Over.mk i), G.w_obj (Over.mk i)⟩

/-- The image under a functor over `C` on the slice `C/U'` of the arrow to the terminal object is
a cartesian lift of `i`: it is even strongly cartesian, by
`CategoryTheory.Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal`. -/
lemma isCartesian_map_sliceToTerminal (p : S ⥤ C) (hp : p.IsFiberedInGroupoids)
    {U U' : C} (i : U ⟶ U')
    (G : BasedCategory.ofFunctor (Over.forget U') ⥤ᵇ BasedCategory.ofFunctor p) :
    p.IsCartesian i (G.map (sliceToTerminal i)) :=
  @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
    (Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal p hp U' G (Over.mk i))

/-- The value at `(U, i)` of a functor over `C` on the slice over `U'` is a chosen pullback along
`i` of its value at the terminal object: both are cartesian lifts of `i` at the same object, so
they are canonically isomorphic in the fibre of `p` over `U`. -/
noncomputable def pullbackFiberTwoYonedaIso (p : S ⥤ C) [p.IsPreFibered]
    (hp : p.IsFiberedInGroupoids) {U U' : C} (i : U ⟶ U')
    (G : BasedCategory.ofFunctor (Over.forget U') ⥤ᵇ BasedCategory.ofFunctor p) :
    p.pullbackFiber ((Functor.twoYonedaEvaluation p U').obj G) i ≅ sliceObjFiber p i G :=
  Functor.fiberIsoOfCartesian (p := p) i
    (Functor.IsPreFibered.pullbackMap ((Functor.twoYonedaEvaluation p U').obj G).2 i)
    (G.map (sliceToTerminal i))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
    (isCartesian_map_sliceToTerminal p hp i G)

/-- A functor sends a composite of three morphisms to the composite of the images. -/
private theorem map_comp_comp {D E : Type*} [Category D] [Category E] (F : D ⥤ E) {X Y Z W : D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) : F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h :=
  (F.map_comp f (g ≫ h)).trans (congrArg (fun z => F.map f ≫ z) (F.map_comp g h))

/-- The component at an object `(U, i)` of the slice of a 2-morphism of functors over `C` is,
through `CategoryTheory.Functor.TwoYoneda.pullbackFiberTwoYonedaIso`, the morphism of chosen
pullbacks induced by its component at the terminal object. -/
lemma twoYonedaEvaluation_app_eq_pullbackFiberHom (p : S ⥤ C) [p.IsPreFibered]
    (hp : p.IsFiberedInGroupoids) {U U' : C} (i : U ⟶ U')
    (G G' : BasedCategory.ofFunctor (Over.forget U') ⥤ᵇ BasedCategory.ofFunctor p)
    (η : G ⟶ G') :
    η.app (Over.mk i) =
      Functor.Fiber.fiberInclusion.map ((pullbackFiberTwoYonedaIso p hp i G).inv ≫
        Functor.pullbackFiberHom ((Functor.twoYonedaEvaluation p U').map η) i ≫
          (pullbackFiberTwoYonedaIso p hp i G').hom) := by
  have hlift : p.IsHomLift (𝟙 U) (η.app (Over.mk i)) := η.isHomLift' (Over.mk i)
  have key : (⟨η.app (Over.mk i), hlift⟩ : sliceObjFiber p i G ⟶ sliceObjFiber p i G') =
      (pullbackFiberTwoYonedaIso p hp i G).inv ≫
        Functor.pullbackFiberHom ((Functor.twoYonedaEvaluation p U').map η) i ≫
          (pullbackFiberTwoYonedaIso p hp i G').hom := by
    refine Functor.fiber_hom_ext_of_cartesian i (G'.map (sliceToTerminal i))
      (isCartesian_map_sliceToTerminal p hp i G') _ _ ?_
    let ev := Functor.twoYonedaEvaluation p U'
    let cG := pullbackFiberTwoYonedaIso p hp i G
    let cG' := pullbackFiberTwoYonedaIso p hp i G'
    let t := sliceToTerminal i
    let P := Functor.IsPreFibered.pullbackMap (ev.obj G).2 i
    let P' := Functor.IsPreFibered.pullbackMap (ev.obj G').2 i
    let e := η.app (Over.mk (𝟙 U'))
    let ph := Functor.pullbackFiberHom (ev.map η) i
    let a := Functor.Fiber.fiberInclusion.map cG.inv
    let b := Functor.Fiber.fiberInclusion.map ph
    let c := Functor.Fiber.fiberInclusion.map cG'.hom
    have hcinv : a ≫ P = G.map t := Functor.fiberIsoOfCartesian_inv_fac i _ _ _ _
    have hc'hom : c ≫ G'.map t = P' := Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
    have hpb : b ≫ P' = P ≫ Functor.Fiber.fiberInclusion.map (ev.map η) :=
      Functor.pullbackFiberHom_fac (ev.map η) i
    have heval : Functor.Fiber.fiberInclusion.map (ev.map η) = e :=
      Functor.twoYonedaEvaluation_map p U' η
    have hsplit : Functor.Fiber.fiberInclusion.map (cG.inv ≫ ph ≫ cG'.hom) = a ≫ b ≫ c :=
      map_comp_comp _ _ _ _
    have s1 : η.app (Over.mk i) ≫ G'.map t = G.map t ≫ e := (η.naturality t).symm
    have s2 : G.map t ≫ e = (a ≫ P) ≫ e := congrArg (fun z => z ≫ e) hcinv.symm
    have s3 : (a ≫ P) ≫ e = a ≫ P ≫ e := Category.assoc _ _ _
    have s4 : a ≫ P ≫ e = a ≫ P ≫ Functor.Fiber.fiberInclusion.map (ev.map η) :=
      congrArg (fun z => a ≫ P ≫ z) heval.symm
    have s5 : a ≫ P ≫ Functor.Fiber.fiberInclusion.map (ev.map η) = a ≫ b ≫ P' :=
      congrArg (fun z => a ≫ z) hpb.symm
    have s6 : a ≫ b ≫ P' = a ≫ b ≫ c ≫ G'.map t :=
      congrArg (fun z => a ≫ b ≫ z) hc'hom.symm
    have s7 : a ≫ b ≫ c ≫ G'.map t = (a ≫ b ≫ c) ≫ G'.map t :=
      (congrArg (fun z => a ≫ z) (Category.assoc b c (G'.map t)).symm).trans
        (Category.assoc a (b ≫ c) (G'.map t)).symm
    have s8 : (a ≫ b ≫ c) ≫ G'.map t =
        Functor.Fiber.fiberInclusion.map (cG.inv ≫ ph ≫ cG'.hom) ≫ G'.map t :=
      congrArg (fun z => z ≫ G'.map t) hsplit.symm
    exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8))))))
  exact congrArg Functor.Fiber.fiberInclusion.map key

/-- `CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_app_eq_pullbackFiberHom` with the
comparison split into its three factors. -/
lemma twoYonedaEvaluation_app_eq_comp (p : S ⥤ C) [p.IsPreFibered]
    (hp : p.IsFiberedInGroupoids) {U U' : C} (i : U ⟶ U')
    (G G' : BasedCategory.ofFunctor (Over.forget U') ⥤ᵇ BasedCategory.ofFunctor p)
    (η : G ⟶ G') :
    η.app (Over.mk i) =
      Functor.Fiber.fiberInclusion.map (pullbackFiberTwoYonedaIso p hp i G).inv ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom ((Functor.twoYonedaEvaluation p U').map η) i) ≫
          Functor.Fiber.fiberInclusion.map (pullbackFiberTwoYonedaIso p hp i G').hom :=
  (twoYonedaEvaluation_app_eq_pullbackFiberHom p hp i G G' η).trans
    (map_comp_comp _ _ _ _)

/-- The component at the terminal object of the 2-morphism obtained, through fullness of the
2-Yoneda evaluation functor, from a morphism of the fibre objects it evaluates to: it is that
morphism. -/
lemma twoYonedaEvaluation_preimage_app (p : S ⥤ C) (U : C)
    (hE : (Functor.twoYonedaEvaluation p U).IsEquivalence)
    {G G' : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : (Functor.twoYonedaEvaluation p U).obj G ⟶
      (Functor.twoYonedaEvaluation p U).obj G') :
    ((Functor.FullyFaithful.ofFullyFaithful (Functor.twoYonedaEvaluation p U)).preimage η).app
        (Over.mk (𝟙 U)) = Functor.Fiber.fiberInclusion.map η := by
  have := hE.full
  have := hE.faithful
  rw [← Functor.twoYonedaEvaluation_map]
  exact congrArg Functor.Fiber.fiberInclusion.map
    ((Functor.FullyFaithful.ofFullyFaithful (Functor.twoYonedaEvaluation p U)).map_preimage η)

end CategoryTheory.Functor.TwoYoneda

end
