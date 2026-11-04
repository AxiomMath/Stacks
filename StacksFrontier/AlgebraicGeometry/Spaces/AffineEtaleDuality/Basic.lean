module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalenceUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Associated modules on the small étale site of an affine scheme

Let `A` be a commutative ring, `X = Spec A`, and let `X_étale` be the small étale site of `X`
inside a big étale site `B`. Write `ε^*T` for the composite of the associated-sheaf functor
`M ↦ M̃` with the associated-module functor `ε^*` of the small étale site, so that
`ε^*T M = ε^* M̃` is the quasi-coherent `𝒪_étale`-module attached to the `A`-module `M`.

This file records the two universal properties of `ε^*T` used in the proof of Stacks 0E50.

* `ε^*T` is left adjoint to the `A`-module of global sections, by composing the adjunctions of
  `M ↦ M̃` and of `ε^*`.
* For an object `V` of the small étale site, morphisms `(ε^*T M)|_V ⟶ H|_V` of modules on the
  slice site over `V` are `A`-linear maps from `M` into the sections of `H` over `V`. The sections
  over `V` are read through the slice adjunction, as the global sections of the pushforward of
  `H|_V` along `Over.star V`; `AlgebraicGeometry.AffineEtaleDuality.secVAddEquiv` identifies them
  additively with the sections of `H` over `V` itself.

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.epsT`: the functor `M ↦ ε^* M̃`.
* `AlgebraicGeometry.AffineEtaleDuality.epsTAdj`: the adjunction `ε^*T ⊣ Γ`.
* `AlgebraicGeometry.AffineEtaleDuality.secV`: the `A`-module of sections over `V`.
* `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquiv`: the universal property on the slice.

## Main results

* `AlgebraicGeometry.AffineEtaleDuality.sliceHomEquiv_apply`: the correspondence evaluates a
  morphism of the slice at `V` on the restriction to `V` of the canonical global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- The small étale site of `Spec A`. -/
abbrev Site := SmallEtale B (Spec A) hX

/-- The structure sheaf of the small étale site of `Spec A`, as the sheaf of rings of the small
étale ringed site. It is `AlgebraicGeometry.SmallEtale.structureSheaf` on the nose. -/
abbrev O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec A) hX).O

/-- `O` is definitionally the structure sheaf of the small étale site of `Spec A`. -/
lemma O_eq_structureSheaf : O A B hX = SmallEtale.structureSheaf B (Spec A) hX := rfl

/-- The structure sheaf of the small étale site of `Spec A`, as a presheaf of commutative rings.
Forgetting commutativity gives `O` on the nose. -/
abbrev Rc := SmallEtale.commStructurePresheaf B (Spec A) hX

/-- The underlying presheaf of `O` is `Rc` composed with the forgetful functor to rings. -/
lemma O_obj_eq : (O A B hX).obj = Rc A B hX ⋙ forget₂ CommRingCat RingCat := rfl

/-- Sheaves of `𝒪`-modules on the small étale site of `Spec A`. -/
abbrev Mod := SheafOfModules.{u} (O A B hX)

/-- The quasi-coherent `𝒪_étale`-module `ε^* M̃` associated to an `A`-module `M`. -/
abbrev epsT : ModuleCat.{u} A ⥤ Mod A B hX :=
  tilde.functor A ⋙ SmallEtale.associatedModule B (Spec A) hX

/-- Global sections of an `𝒪_étale`-module, as an `A`-module: the sections over the open `⊤`
read as an object of the small étale site. -/
abbrev gammaTop : Mod A B hX ⥤ ModuleCat.{u} A :=
  SmallEtale.restrictModule B (Spec A) hX ⋙ moduleSpecΓFunctor

/-- **`ε^*T ⊣ Γ`.** The composite of the adjunction `M ↦ M̃ ⊣ Γ` with `ε^* ⊣ ε_*`. -/
def epsTAdj : epsT A B hX ⊣ gammaTop A B hX :=
  tilde.adjunction.comp (SmallEtale.associatedModuleAdjunction B (Spec A) hX)

/-- The open `⊤` of `Spec A`, as an object of the small étale site. It is a final object. -/
abbrev top : Site A B hX := SmallEtale.opensObj B (Spec A) hX ⊤

/-- The open `⊤` is a final object of the small étale site. -/
def topIsTerminal : IsTerminal (top A B hX) := SmallEtale.isTerminalOpensObjTop B (Spec A) hX

/-- The unique morphism from an object of the small étale site to the final object `⊤`. -/
def toTop (V : Site A B hX) : V ⟶ top A B hX := (topIsTerminal A B hX).from V

/-- Any two morphisms into the final object agree. -/
lemma toTop_eq {V : Site A B hX} (f : V ⟶ top A B hX) : f = toTop A B hX V :=
  (topIsTerminal A B hX).hom_ext _ _

/-- The canonical global section of `ε^* M̃` attached to an element of `M`: the unit of
`ε^*T ⊣ Γ`. -/
def unitSection (M : ModuleCat.{u} A) (m : M) :
    ((epsT A B hX).obj M).val.obj (op (top A B hX)) :=
  ((epsTAdj A B hX).unit.app M).hom m

/-- The restriction to `V` of the canonical global section attached to `m`. -/
def unitSectionAt (M : ModuleCat.{u} A) (V : Site A B hX) (m : M) :
    ((epsT A B hX).obj M).val.obj (op V) :=
  ((epsT A B hX).obj M).val.map (toTop A B hX V).op (unitSection A B hX M m)

/-! ### Sections over an object -/

/-- The sections of an `𝒪_étale`-module over `V`, as an `A`-module, read through the slice
adjunction: global sections of the pushforward along `Over.star V` of the restriction to `V`. -/
abbrev secV (V : Site A B hX) : Mod A B hX ⥤ ModuleCat.{u} A :=
  SheafOfModules.overFunctor (O A B hX) V ⋙
    SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver V) ⋙ gammaTop A B hX

/-- The section of `secV V` is a section over `V ⨯ ⊤`. -/
lemma secV_obj_eq (V : Site A B hX) (H : Mod A B hX) :
    (((secV A B hX V).obj H : ModuleCat.{u} A) : Type u) = H.val.obj (op (V ⨯ top A B hX)) :=
  rfl

/-- The morphism `V ⟶ V ⨯ ⊤` given by the identity and the unique morphism to `⊤`. -/
def toProdTop (V : Site A B hX) : V ⟶ V ⨯ top A B hX := prod.lift (𝟙 V) (toTop A B hX V)

/-- `toProdTop V` followed by the first projection is the identity of `V`. -/
lemma toProdTop_fst (V : Site A B hX) : toProdTop A B hX V ≫ prod.fst = 𝟙 V := prod.lift_fst _ _

/-- The first projection `V ⨯ ⊤ ⟶ V` followed by `toProdTop V` is the identity of `V ⨯ ⊤`. -/
lemma prod_fst_toProdTop (V : Site A B hX) :
    (prod.fst : V ⨯ top A B hX ⟶ V) ≫ toProdTop A B hX V = 𝟙 _ := by
  apply prod.hom_ext
  · simp [toProdTop]
  · exact (topIsTerminal A B hX).hom_ext _ _

/-- `V ≅ V ⨯ ⊤`, the final object `⊤` being a unit for the product. -/
def prodTopIso (V : Site A B hX) : V ≅ V ⨯ top A B hX where
  hom := toProdTop A B hX V
  inv := prod.fst
  hom_inv_id := toProdTop_fst A B hX V
  inv_hom_id := prod_fst_toProdTop A B hX V

/-- The sections of `secV V` are the sections over `V`, additively. -/
def secVAddEquiv (V : Site A B hX) (H : Mod A B hX) :
    ((secV A B hX V).obj H : Type u) ≃+ H.val.obj (op V) :=
  (H.val.presheaf.mapIso (prodTopIso A B hX V).op).addCommGroupIsoToAddEquiv

/-- `secVAddEquiv` is restriction along `toProdTop V`. -/
lemma secVAddEquiv_apply (V : Site A B hX) (H : Mod A B hX) (x : (secV A B hX V).obj H) :
    secVAddEquiv A B hX V H x = H.val.presheaf.map (toProdTop A B hX V).op x := rfl

/-- `secVAddEquiv` is natural in the module `H`. -/
lemma secVAddEquiv_naturality (V : Site A B hX) {H H' : Mod A B hX} (f : H ⟶ H')
    (x : (secV A B hX V).obj H) :
    secVAddEquiv A B hX V H' ((secV A B hX V).map f x) =
      f.val.app (op V) (secVAddEquiv A B hX V H x) :=
  (PresheafOfModules.naturality_apply f.val (toProdTop A B hX V).op x).symm

/-! ### The universal property on the slice -/

/-- The structure morphism of `Over.star V` at `⊤` is the first projection. -/
lemma star_obj_top_hom (V : Site A B hX) :
    ((Over.star V).obj (top A B hX)).hom = prod.fst := by
  simp only [Over.star_obj_hom]
  exact prod.lift_fst _ _

/-- **Morphisms out of the restriction of `ε^*T M` to `V` are `A`-linear maps out of `M`.** For an
`A`-module `M`, an `𝒪_étale`-module `H` and an object `V` of the small étale site, morphisms
`(ε^*T M)|_V ⟶ H|_V` of modules on the slice site over `V` correspond to `A`-linear maps from `M`
to the sections of `H` over `V`. -/
def sliceHomEquiv (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX) :
    (((epsT A B hX).obj M).over V ⟶ H.over V) ≃ (M ⟶ (secV A B hX V).obj H) :=
  ((SheafOfModules.overPushforwardOverAdj V).homEquiv _ _).trans
    ((epsTAdj A B hX).homEquiv _ _)

/-- The correspondence `sliceHomEquiv` evaluates a morphism at `V` on the restriction to `V` of
the canonical global sections. -/
lemma sliceHomEquiv_apply (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX)
    (φ : ((epsT A B hX).obj M).over V ⟶ H.over V) (m : M) :
    secVAddEquiv A B hX V H (sliceHomEquiv A B hX M H V φ m) =
      φ.val.app (op (Over.mk (𝟙 V))) (unitSectionAt A B hX M V m) := by
  let E := (epsT A B hX).obj M
  let f : Over.mk (𝟙 V) ⟶ (Over.star V).obj (top A B hX) :=
    Over.homMk (toProdTop A B hX V) (by rw [star_obj_top_hom]; exact toProdTop_fst A B hX V)
  have h2 := PresheafOfModules.naturality_apply φ.val f.op
    (E.val.map (prod.snd : V ⨯ top A B hX ⟶ top A B hX).op (unitSection A B hX M m))
  show H.val.presheaf.map (toProdTop A B hX V).op
      (φ.val.app (op ((Over.star V).obj (top A B hX)))
        (E.val.map (prod.snd : V ⨯ top A B hX ⟶ top A B hX).op (unitSection A B hX M m))) = _
  refine h2.symm.trans ?_
  congr 1
  show (E.val.presheaf.map (prod.snd : V ⨯ top A B hX ⟶ top A B hX).op ≫
      E.val.presheaf.map (toProdTop A B hX V).op) (unitSection A B hX M m) = _
  rw [← CategoryTheory.Functor.map_comp, ← op_comp, toTop_eq A B hX (toProdTop A B hX V ≫ _)]
  rfl

end AlgebraicGeometry.AffineEtaleDuality

end
