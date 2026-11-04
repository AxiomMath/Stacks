module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomTensorIso
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomFirstVariable

/-!
# Precomposition on the internal Hom sheaf is the conjugate of the tensor whiskering

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `k : F' ⟶ F` be a morphism of
sheaves of `O`-modules. Tensoring by `F` is left adjoint to the internal Hom functor
`Hom_O(F, -)` of Stacks 03EM, and likewise for `F'` (the sheaf clause of Stacks 03EO,
`Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction`). Whiskering by `k` is a natural
transformation `F' ⊗_O - ⟶ F ⊗_O -` of the two left adjoints, so it has a conjugate natural
transformation `Hom_O(F, -) ⟶ Hom_O(F', -)` of the two right adjoints
(`CategoryTheory.conjugateEquiv`). This file identifies that conjugate: it is precomposition by
`k` on the internal Hom sheaf, the contravariant functoriality of Stacks 03EN in the first
variable.

Together with `Stacks.SheafOfModules.InternalHom.pre_comp_ihomIsoInternalHomSecondFunctor`,
which carries `CategoryTheory.MonoidalClosed.pre k` across the internal-Hom bridge to exactly
this conjugate, this says that `pre k` on the monoidal-closed internal hom of sheaves of
`O`-modules is precomposition by `k` on Stacks 03EM's internal Hom sheaf.

## Main definitions

* `Stacks.SheafOfModules.InternalHom.internalHomMapLeftNatTrans`: precomposition in the first
  variable of the internal Hom sheaf, assembled as a natural transformation
  `Hom_O(F, -) ⟶ Hom_O(F', -)` of the internal-Hom functors of Stacks 03EN.

## Main results

* `Stacks.SheafOfModules.InternalHom.conjugateEquiv_tensoringLeft_map`: **the
  identification.** The conjugate of `k ▷ -` under the two tensor--internal-Hom adjunctions of
  Stacks 03EO is `internalHomMapLeftNatTrans`, and
  `Stacks.SheafOfModules.InternalHom.conjugateEquiv_tensoringLeft_map_app` reads that off at a
  fixed target: the component at `H` is `sheafInternalHomMapLeft`.
* `Stacks.SheafOfModules.InternalHom.homEquiv_comp_sheafInternalHomMapLeft`: the content of the
  identification, that precomposition by `k` commutes with the two currying bijections.
* `Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction_homEquiv_val`: the currying bijection
  of the left-handed re-seated adjunction, on underlying presheaves of modules, in terms of the
  presheaf-level currying of Stacks 03EO.
* `CategoryTheory.conjugateEquiv_eq_of_homEquiv`: a conjugate natural transformation is pinned
  down by its compatibility with the two hom-equivalences.
* `Stacks.PresheafOfModules.InternalHom.curryGlobal_comp_internalHomMapLeft`: the presheaf
  analogue, proved on sections.

## Implementation notes

A conjugate transformation `γ : R₁ ⟶ R₂` of right adjoints is characterised by
`adj₁.homEquiv c X f ≫ γ.app X = adj₂.homEquiv c X (α.app c ≫ f)`
(`CategoryTheory.conjugateEquiv_eq_of_homEquiv`), which involves only the units of the two
adjunctions; the counit of `tensorLeftAdjunction` is built from sheafification and is not
described on sections.

Stacks 03EO is stated for `- ⊗_O G`, so its currying is right-handed, whereas
`MonoidalClosed.ihom` and hence `tensorLeftAdjunction` are left-handed; the two differ by the
symmetry of presheaves of modules,
`Stacks.PresheafOfModules.InternalHom.tensoringRightIsoTensorLeft`.

Two spellings of the underlying presheaf of rings are in play, `Oforget R.obj` and
`(Stacks.SheafOfModules.Tensor.ringSheaf R).obj`, and with them two spellings of the monoidal
structure on presheaves of modules. They agree definitionally but not syntactically, so where
presheaf-level and sheaf-level terms meet the proofs use `Eq.trans` and `congrArg` rather than
rewriting.

**Universe narrowing, inherited from the chain and recorded rather than decided here.** The
statements are at ring universe `max u v` and module universe `max u v` for a site with objects
in `Type u` and morphisms in `Type v`, the narrowing already carried by
`Stacks.SheafOfModules.InternalHom.tensorLeftAdjunction` and by
`SheafOfModules.monoidalClosed`: the monoidal structure on sheaves of modules whose
tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor` exists only there.

Nothing here is tagged: these statements belong to the covering set of a clause of Stacks 03EO,
and the tag is placed once over a clause's whole covering set.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

noncomputable section

namespace CategoryTheory

section Conjugate

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- **A conjugate transformation is compatible with the two hom-equivalences.** For
`α : L₂ ⟶ L₁` between left adjoints, transposing a morphism `f` out of `L₁.obj c` and then
applying the conjugate of `α` is transposing `α.app c ≫ f`. -/
theorem homEquiv_comp_conjugateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (c : C) (X : D) (f : L₁.obj c ⟶ X) :
    adj₁.homEquiv c X f ≫ (conjugateEquiv adj₁ adj₂ α).app X =
      adj₂.homEquiv c X (α.app c ≫ f) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality f, ← Category.assoc,
    unit_conjugateEquiv adj₁ adj₂ α c, Category.assoc, ← Functor.map_comp]

/-- **That compatibility pins the conjugate down.** A natural transformation `γ : R₁ ⟶ R₂` of
right adjoints which is compatible with the two hom-equivalences, in the sense of
`CategoryTheory.homEquiv_comp_conjugateEquiv`, is the conjugate of `α`. -/
theorem conjugateEquiv_eq_of_homEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    (γ : R₁ ⟶ R₂)
    (h : ∀ (c : C) (X : D) (f : L₁.obj c ⟶ X),
      adj₁.homEquiv c X f ≫ γ.app X = adj₂.homEquiv c X (α.app c ≫ f)) :
    conjugateEquiv adj₁ adj₂ α = γ := by
  ext X
  have e : adj₁.homEquiv (R₁.obj X) X (adj₁.counit.app X) = 𝟙 (R₁.obj X) := by
    rw [Adjunction.homEquiv_unit]
    exact adj₁.right_triangle_components X
  have h1 := h (R₁.obj X) X (adj₁.counit.app X)
  have h2 := homEquiv_comp_conjugateEquiv adj₁ adj₂ α (R₁.obj X) X (adj₁.counit.app X)
  rw [e, Category.id_comp] at h1 h2
  exact h2.trans h1.symm

end Conjugate

end CategoryTheory

namespace Stacks.PresheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v})

/-- **Presheaf currying is contravariantly natural in the internal-Hom source.** For
`k : G' ⟶ G`, currying a morphism `b : F ⊗ G ⟶ H` and then precomposing by `k` on the internal
Hom presheaf of Stacks 03EM is currying `(F ◁ k) ≫ b`. -/
theorem curryGlobal_comp_internalHomMapLeft
    (F H : _root_.PresheafOfModules.{max u v} (Oforget O))
    {G G' : _root_.PresheafOfModules.{max u v} (Oforget O)} (k : G' ⟶ G)
    (b : F ⊗ G ⟶ H) :
    curryGlobal O F G H b ≫ internalHomMapLeft O k =
      curryGlobal O F G' H ((F ◁ k) ≫ b) := by
  refine _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ ?_
  refine _root_.PresheafOfModules.hom_ext fun V ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦ ?_
  exact (curryGlobalMap_apply O F G H b X.unop x V.unop.hom (k.app (op V.unop.left) y)).trans
    (curryGlobalMap_apply O F G' H ((F ◁ k) ≫ b) X.unop x V.unop.hom y).symm

/-- **The braiding of presheaves of modules is natural in its fixed factor.** Whiskering by
`k : M' ⟶ M` on the right of `N` and then braiding is braiding and then whiskering by `k` on
the left of `N`. -/
theorem whiskerLeft_comp_tensoringRightIsoTensorLeft
    (N : _root_.PresheafOfModules.{max u v} (Oforget O))
    {M M' : _root_.PresheafOfModules.{max u v} (Oforget O)} (k : M' ⟶ M) :
    (N ◁ k) ≫ (tensoringRightIsoTensorLeft O M).hom.app N =
      (tensoringRightIsoTensorLeft O M').hom.app N ≫ (k ▷ N) :=
  BraidedCategory.braiding_naturality_right N k

end Stacks.PresheafOfModules.InternalHom

namespace Stacks.SheafOfModules.InternalHom

open Stacks.PresheafOfModules.InternalHom

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{max u v})
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

/-- **The currying bijection of Stacks 03EO, left-handed, on underlying presheaves.** A
morphism `f : F ⊗_O G ⟶ H` of sheaves of modules is sent to the presheaf-level currying of `f`,
read through the braiding and the unit of module sheafification. -/
theorem tensorLeftAdjunction_homEquiv_val
    (F G H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (f : (tensorLeft F).obj G ⟶ H) :
    ((tensorLeftAdjunction R F).homEquiv G H f).val =
      curryGlobal R.obj G.val F.val H.val
        ((tensoringRightIsoTensorLeft R.obj F.val).hom.app G.val ≫
          (sheafifyForgetAdjunction R).homEquiv _ H
            ((_root_.SheafOfModules.sheafTensorIso R F G).inv ≫ f)) :=
  rfl

/-- **Currying commutes with precomposition on the internal Hom sheaf.** For `k : F' ⟶ F`,
transposing `f : F ⊗_O G ⟶ H` across the adjunction for `F` and then precomposing by `k` on the
internal Hom sheaf is transposing `(k ▷ G) ≫ f` across the adjunction for `F'`. -/
theorem homEquiv_comp_sheafInternalHomMapLeft
    {F F' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (k : F' ⟶ F)
    (G H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (f : (tensorLeft F).obj G ⟶ H) :
    (tensorLeftAdjunction R F).homEquiv G H f ≫ sheafInternalHomMapLeft J R k =
      (tensorLeftAdjunction R F').homEquiv G H (((tensoringLeft _).map k).app G ≫ f) := by
  have h3 : (PresheafOfModules.sheafification
      (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf R)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map
          ((_root_.SheafOfModules.forget _).map k ▷
            (_root_.SheafOfModules.forget _).obj G) ≫
        (_root_.SheafOfModules.sheafTensorIso R F G).inv =
      (_root_.SheafOfModules.sheafTensorIso R F' G).inv ≫ k ▷ G := by
    rw [Iso.comp_inv_eq, Category.assoc,
      _root_.SheafOfModules.sheafTensorIso_naturality_left R k G, Iso.inv_hom_id_assoc]
  refine _root_.SheafOfModules.hom_ext ?_
  have e1 : ∀ a : G ⟶ (internalHomSecondFunctor.{v, u, max u v, u} J R F).obj H,
      (a ≫ sheafInternalHomMapLeft J R k).val =
        a.val ≫ internalHomMapLeft R.obj k.val := fun _ ↦ rfl
  rw [e1, tensorLeftAdjunction_homEquiv_val, tensorLeftAdjunction_homEquiv_val]
  refine Eq.trans (curryGlobal_comp_internalHomMapLeft R.obj G.val H.val k.val _) ?_
  refine congrArg (curryGlobal R.obj G.val F'.val H.val) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z ↦ z ≫
      (sheafifyForgetAdjunction R).homEquiv _ H
        ((_root_.SheafOfModules.sheafTensorIso R F G).inv ≫ f))
    (whiskerLeft_comp_tensoringRightIsoTensorLeft R.obj G.val k.val)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg
    (fun z ↦ (tensoringRightIsoTensorLeft R.obj F'.val).hom.app G.val ≫ z) ?_
  refine Eq.trans
    (Adjunction.homEquiv_naturality_left (sheafifyForgetAdjunction R) _ _).symm ?_
  refine congrArg (fun z ↦ (sheafifyForgetAdjunction R).homEquiv _ H z) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Eq.trans (congrArg (fun z ↦ z ≫ f) h3) (Category.assoc _ _ _)

/-- **Precomposition in the first variable of the internal Hom sheaf, as a natural
transformation.** For `k : F' ⟶ F` the maps `sheafInternalHomMapLeft` are the components of a
natural transformation `Hom_O(F, -) ⟶ Hom_O(F', -)` between the internal-Hom functors of
Stacks 03EN. -/
def internalHomMapLeftNatTrans
    {F F' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (k : F' ⟶ F) :
    internalHomSecondFunctor.{v, u, max u v, u} J R F ⟶
      internalHomSecondFunctor.{v, u, max u v, u} J R F' where
  app _ := sheafInternalHomMapLeft J R k
  naturality _ _ _ := _root_.SheafOfModules.hom_ext <| _root_.PresheafOfModules.hom_ext
    fun _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ rfl

/-- **The conjugate of the tensor whiskering is precomposition on the internal Hom sheaf.**
Tensoring by `F` and by `F'` are left adjoint to the internal Hom functors out of `F` and out
of `F'`, so a morphism `k : F' ⟶ F` gives, through `k ▷ -`, a natural transformation
`Hom_O(F, -) ⟶ Hom_O(F', -)`; it is precomposition by `k`, the contravariant functoriality of
Stacks 03EN in the first variable. -/
theorem conjugateEquiv_tensoringLeft_map
    {F F' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (k : F' ⟶ F) :
    conjugateEquiv (tensorLeftAdjunction R F) (tensorLeftAdjunction R F')
        ((tensoringLeft _).map k) = internalHomMapLeftNatTrans R k :=
  conjugateEquiv_eq_of_homEquiv _ _ _ _
    (fun G H f ↦ homEquiv_comp_sheafInternalHomMapLeft R k G H f)

/-- **The same identification at a fixed target.** The component at `H` of the conjugate of
`k ▷ -` is precomposition by `k` on the internal Hom sheaves with target `H`. -/
theorem conjugateEquiv_tensoringLeft_map_app
    {F F' : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    (k : F' ⟶ F)
    (H : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (conjugateEquiv (tensorLeftAdjunction R F) (tensorLeftAdjunction R F')
        ((tensoringLeft _).map k)).app H = sheafInternalHomMapLeft J R k :=
  congrArg (fun γ ↦ γ.app H) (conjugateEquiv_tensoringLeft_map R k)

end Stacks.SheafOfModules.InternalHom

end

end
