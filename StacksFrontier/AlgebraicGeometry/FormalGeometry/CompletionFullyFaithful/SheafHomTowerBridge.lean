module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PullbackSheafHom
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerUnitHoms

/-!
# Condition (3) at the internal hom is condition (4)

Condition (3) of [Stacks, Tag 0EK2] compares, for one module `ℰ`, the colimit of the sections
`Γ(W, ℰ)` over the open neighbourhoods `W` of a closed subscheme with the inverse limit of the
sections on its infinitesimal neighbourhoods; condition (4) compares, for two modules `𝒢` and `ℱ`,
the colimit of the morphisms `𝒢|_W ⟶ ℱ|_W` with the inverse limit of the morphisms
`𝒢|_{Y_n} ⟶ ℱ|_{Y_n}`. Taking `ℰ = ℋom(𝒢, ℱ)` turns the first comparison into the second, because
a morphism between the restrictions of `𝒢` and `ℱ` is a section of the internal hom. This file
carries that out for an abstract `Stacks.Algebraization.InfinitesimalTower`, and so proves the
implication `(3) ⇒ (4)`.

The identification needed is a single family: for a morphism of schemes `f : A ⟶ Z`, a global
section of `f^* ℋom(𝒢, ℱ)` is a morphism `f^* 𝒢 ⟶ f^* ℱ`. It is built from the canonical
comparison `f^* ℋom(𝒢, ℱ) ⟶ ℋom(f^* 𝒢, f^* ℱ)` of [Stacks, Tag 0GMX], read on global sections
and followed by the identification of the global sections of an internal hom with the morphisms.
What the bookkeeping of
`Stacks.Algebraization.InfinitesimalTower.isHomsComplete_of_isSectionsComplete` asks of such a
family is that it be bijective and natural in `f`; **naturality is proved here**, and
bijectivity is exactly the invertibility of the comparison of [Stacks, Tag 0GMX], which for
`𝒢` finite locally free is the one statement the library is missing — see the implementation
notes.

## Main definitions

* `Stacks.Algebraization.sheafHomConj` — conjugation `ℋom(G₁, F₁) ⟶ ℋom(G₂, F₂)` of the internal
  hom by a morphism in each variable.
* `Stacks.Algebraization.pullbackSheafHomSection` — **the family**: the morphism
  `f^* 𝒢 ⟶ f^* ℱ` attached to a global section of `f^* ℋom(𝒢, ℱ)`.

## Main results

* `Stacks.Algebraization.hom_ext_sheafHom_pullback` — extensionality for morphisms from a pullback
  into an internal hom, with both test sections canonical images.
* `Stacks.Algebraization.pullbackSheafHomMap_factor` — **the canonical comparison of
  [Stacks, Tag 0GMX] is natural in the morphism of schemes.** This is the compatibility the
  library had for the dual (`Stacks.Chow.pullbackDualMap_comp`) and for the tensor comparison
  (`Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp`) and not for the internal
  hom.
* `Stacks.Algebraization.pullbackSheafHomSection_factor` — the family is natural in the morphism.
* `Stacks.Algebraization.InfinitesimalTower.isHomsComplete_of_isSectionsComplete_of_homEquiv` —
  the bookkeeping: a bijective natural family turns condition (3) for `ℰ` into condition (4) for
  the pair `(𝒢, ℱ)`.
* `Stacks.Algebraization.InfinitesimalTower.IsHomsComplete.of_isSectionsComplete_sheafHom_of_isIso`
  and `...of_isSectionsComplete_sheafHom` — **the implication (3) ⇒ (4)**, the first granted that
  the comparison of [Stacks, Tag 0GMX] is invertible, the second granted the identification of
  that comparison with the isomorphism `Stacks.Algebraization.pullbackSheafHomIso`, which exists
  for `𝒢` finite locally free.

## Implementation notes

**What is not proved here.** `Stacks.Algebraization.pullbackSheafHomIso` of
`PullbackSheafHom.lean` is an isomorphism `f^* ℋom(𝒢, ℱ) ≅ ℋom(f^* 𝒢, f^* ℱ)` for `𝒢` finite
locally free, assembled from the rank-one description `ℋom(𝒢, ℱ) ≅ ℱ ⊗ 𝒢^∨`, the tensor
comparison of [Stacks, Tag 01CD] and the dual base-change isomorphism
`Stacks.Chow.pullbackDualMap_isIso`; it is not known to *be* the canonical comparison
`Stacks.Algebraization.pullbackSheafHomMap`, and that identity is the hypothesis `hid` of
`IsHomsComplete.of_isSectionsComplete_sheafHom`. Proving it means computing both morphisms on the
canonical image of a local section of `ℱ ⊗ 𝒢^∨`: the canonical one is computed there by
`Stacks.Algebraization.pullbackSheafHomMap_unit_eval`, and the rank-one one by
`Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection` — but only on a *pure* tensor,
whereas the extensionality that makes the canonical side computable,
`Stacks.Chow.tensor_hom_ext_of_pullbackUnit`, hands over an arbitrary local section of the tensor
product. Closing that step needs the local decomposition of a section of a tensor product into
pure tensors, which is internal to the proofs of that extensionality and is not available as a
statement. Nothing else is missing: naturality in the morphism, which the same circle of ideas
also lacked, is `pullbackSheafHomMap_factor` below.

The naturality proof never computes the comparison on an arbitrary section. Both sides of
`pullbackSheafHomMap_factor` are morphisms out of a pullback into an internal hom, and
`hom_ext_sheafHom_pullback` reduces such an identity to canonical images in *both* slots — the
section of the internal hom and the section it is evaluated on — which is precisely the shape
`Stacks.Algebraization.pullbackSheafHomMap_unit_eval` computes. The two identifications of
iterated pullbacks are moved past the canonical images by
`Stacks.Algebraization.pullbackComp_unit_apply`.

As elsewhere in this directory the proofs are in term mode: `rw` cannot cross the semireducible
projection separating `Γ(ℳ, U)` from the sections of the underlying presheaf, so `Eq.trans`,
`congrArg`, `CategoryTheory.ConcreteCategory.congr_hom` and
`CategoryTheory.ConcreteCategory.comp_apply` are used in its place. Every step is a named lemma
with a written-out statement: with the chain inlined the elaborator times out in `whnf`.
Morphisms are written out with a factorization equation supplied rather than as morphisms of
`CategoryTheory.Over Z`, for the reason recorded in `TowerHoms.lean`.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

/-- **Extensionality for morphisms from a pullback into an internal hom.** Two morphisms
`f^* N ⟶ ℋom(f^* G, P)` agree as soon as, for every open `V` of the target and every pair of
sections of `N` and of `G` over `V`, the local morphism they attach to the canonical image of the
first agrees on the canonical image of the second.

Currying turns such a morphism into a pairing `f^* N ⊗ f^* G ⟶ P`, and a pairing out of a tensor
product of two pullbacks along one morphism is determined by its values on the pure tensors of
canonical images, which is `Stacks.Chow.tensor_hom_ext_of_pullbackUnit`; the value there is the
local morphism evaluated at the terminal object of the slice site, by the characterisation
`Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry` of currying. Both test sections being
canonical images is what makes this usable: the comparison of [Stacks, Tag 0GMX] is computed on
canonical images by `Stacks.Algebraization.pullbackSheafHomMap_unit_eval`. -/
public theorem hom_ext_sheafHom_pullback {A B : Scheme.{u}} (f : A ⟶ B) (N G : B.Modules)
    {P : A.Modules}
    {p q : (Scheme.Modules.pullback f).obj N ⟶
      (sheafHomFunctor A ((Scheme.Modules.pullback f).obj G)).obj P}
    (h : ∀ (V : B.Opens) (n : Γ(N, V)) (m : Γ(G, V)),
      ((p.val.app (op (f ⁻¹ᵁ V))
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
                (op V) n)).app (op (Over.mk (𝟙 (f ⁻¹ᵁ V))))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op V) m) =
        ((q.val.app (op (f ⁻¹ᵁ V))
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
                (op V) n)).app (op (Over.mk (𝟙 (f ⁻¹ᵁ V))))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op V) m)) :
    p = q := by
  have hcurry : ∀ r : (Scheme.Modules.pullback f).obj N ⟶
        (sheafHomFunctor A ((Scheme.Modules.pullback f).obj G)).obj P,
      ∀ (V : B.Opens) (n : Γ(N, V)) (m : Γ(G, V)),
      ((Stacks.SheafOfModules.tensorHomEquiv A.toRingedSpace
            ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj G) P).symm
          r).val.app (op (f ⁻¹ᵁ V))
          (Stacks.Chow.tensorSheafPure A ((Scheme.Modules.pullback f).obj N)
            ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)
            ((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V) n)
              ⊗ₜ[A.presheaf.obj (op (f ⁻¹ᵁ V))]
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app
                (op V) m))) =
        ((r.val.app (op (f ⁻¹ᵁ V))
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
                (op V) n)).app (op (Over.mk (𝟙 (f ⁻¹ᵁ V))))).hom
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op V) m) := by
    intro r V n m
    refine Eq.trans ?_ (congrArg (fun z => ((z.val.app (op (f ⁻¹ᵁ V))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V) n)).app
          (op (Over.mk (𝟙 (f ⁻¹ᵁ V))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).val.app (op V) m))
      ((Stacks.SheafOfModules.tensorHomEquiv A.toRingedSpace
        ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj G)
        P).apply_symm_apply r))
    exact (Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry A.toRingedSpace
      ((Stacks.SheafOfModules.tensorHomEquiv A.toRingedSpace
        ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj G) P).symm r)
      (f ⁻¹ᵁ V) _ _).symm
  refine (Stacks.SheafOfModules.tensorHomEquiv A.toRingedSpace
    ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj G) P).symm.injective ?_
  refine Stacks.Chow.tensor_hom_ext_of_pullbackUnit f N G (fun V n m => ?_)
  exact (hcurry p V n m).trans ((h V n m).trans (hcurry q V n m).symm)

/-- **Conjugation of the internal hom.** The morphism `ℋom(G₁, F₁) ⟶ ℋom(G₂, F₂)` attached to
`α : G₂ ⟶ G₁` and `φ : F₁ ⟶ F₂`: precomposition with `α` in the first variable, which is
`Stacks.SheafOfModules.sheafHomMapLeft`, followed by postcomposition with `φ` in the second,
which is `Stacks.SheafOfModules.sheafHomMapRight`. The library has the two one-variable actions
and not their composite. -/
public def sheafHomConj {A : Scheme.{u}} {G₁ G₂ F₁ F₂ : A.Modules} (α : G₂ ⟶ G₁) (φ : F₁ ⟶ F₂) :
    (sheafHomFunctor A G₁).obj F₁ ⟶ (sheafHomFunctor A G₂).obj F₂ :=
  Stacks.SheafOfModules.sheafHomMapLeft A.toRingedSpace α ≫
    Stacks.SheafOfModules.sheafHomMapRight A.toRingedSpace φ

/-- **The conjugate of a local section of the internal hom is the conjugate of its components.**
At an object `W` of the slice site, the component of the conjugate is the component of the
section, precomposed with `α` and postcomposed with `φ` over `W.left`. -/
public theorem sheafHomConj_app_apply {A : Scheme.{u}} {G₁ G₂ F₁ F₂ : A.Modules} (α : G₂ ⟶ G₁)
    (φ : F₁ ⟶ F₂) (V : A.Opens) (σ : ((sheafHomFunctor A G₁).obj F₁).val.obj (op V))
    (W : Over V) (ξ : Γ(G₂, W.left)) :
    (((sheafHomConj α φ).val.app (op V) σ).app (op W)).hom ξ =
      φ.val.app (op W.left) ((σ.app (op W)).hom (α.val.app (op W.left) ξ)) := rfl

/-- **Conjugation on global sections is conjugation of morphisms.** The morphism
`G₂ ⟶ F₂` attached to the conjugate of a global section of `ℋom(G₁, F₁)` is `α`, followed by the
morphism `G₁ ⟶ F₁` that section attaches, followed by `φ`. -/
public theorem internalHomSectionsTopEquiv_sheafHomConj {A : Scheme.{u}}
    {G₁ G₂ F₁ F₂ : A.Modules} (α : G₂ ⟶ G₁) (φ : F₁ ⟶ F₂)
    (σ : ((sheafHomFunctor A G₁).obj F₁).val.obj (op (⊤ : A.Opens))) :
    internalHomSectionsTopEquiv G₂ F₂ ((sheafHomConj α φ).val.app (op (⊤ : A.Opens)) σ) =
      α ≫ internalHomSectionsTopEquiv G₁ F₁ σ ≫ φ := by
  ext V x
  have hL := congrArg (fun k => k.hom x) (internalHomSectionsTopEquiv_app G₂ F₂
    ((sheafHomConj α φ).val.app (op (⊤ : A.Opens)) σ)
    (Over.mk (homOfLE (le_top : V ≤ (⊤ : A.Opens)))))
  have hR := congrArg (fun k => k.hom (α.val.app (op V) x))
    (internalHomSectionsTopEquiv_app G₁ F₁ σ
      (Over.mk (homOfLE (le_top : V ≤ (⊤ : A.Opens)))))
  refine hL.trans ?_
  refine Eq.trans (sheafHomConj_app_apply α φ ⊤ σ
    (Over.mk (homOfLE (le_top : V ≤ (⊤ : A.Opens)))) x) ?_
  exact congrArg (fun z => φ.val.app (op V) z) hR.symm

/-- **The comparison of a trivial factorization carries an iterated canonical image to the
canonical image along the composite.** This is
`Stacks.Algebraization.pullbackObjFactorIso_rfl_hom_app_apply` followed by
`Stacks.Algebraization.pullbackComp_unit_apply`, read with the units written out. -/
public theorem pullbackObjFactorIso_hom_unit {Z A B : Scheme.{u}} (M : Z.Modules) (b : B ⟶ Z)
    (g : A ⟶ B) (U : Z.Opens) (t : Γ(M, U)) :
    (pullbackObjFactorIso M g (rfl : g ≫ b = g ≫ b)).hom.val.app (op (g ⁻¹ᵁ (b ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pullback b).obj M)).val.app (op (b ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).val.app (op U) t)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app M).val.app (op U) t :=
  (pullbackObjFactorIso_rfl_hom_app_apply g b M (g ⁻¹ᵁ (b ⁻¹ᵁ U)) _).trans
    (pullbackComp_unit_apply g b M U t)

/-- An isomorphism of modules followed by its inverse is the identity on sections. -/
private theorem inv_app_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (x : Γ(M, U)) : e.inv.app U (e.hom.app U x) = x :=
  (ConcreteCategory.congr_hom (congrArg (fun χ => Scheme.Modules.Hom.app χ U) e.hom_inv_id) x).trans
    (CategoryTheory.id_apply _)

/-- The previous identity read backwards: the inverse comparison carries the canonical image
along the composite to the iterated canonical image. -/
public theorem pullbackObjFactorIso_inv_unit {Z A B : Scheme.{u}} (M : Z.Modules) (b : B ⟶ Z)
    (g : A ⟶ B) (U : Z.Opens) (t : Γ(M, U)) :
    (pullbackObjFactorIso M g (rfl : g ≫ b = g ≫ b)).inv.val.app (op (g ⁻¹ᵁ (b ⁻¹ᵁ U)))
        (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app M).val.app (op U) t) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pullback b).obj M)).val.app (op (b ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).val.app (op U) t) := by
  refine Eq.trans (congrArg (fun z => (pullbackObjFactorIso M g
      (rfl : g ≫ b = g ≫ b)).inv.val.app (op (g ⁻¹ᵁ (b ⁻¹ᵁ U))) z)
    (pullbackObjFactorIso_hom_unit M b g U t).symm) ?_
  exact inv_app_hom_app (pullbackObjFactorIso M g (rfl : g ≫ b = g ≫ b))
    (g ⁻¹ᵁ (b ⁻¹ᵁ U)) _

/-- The last two factors of the composite of
`Stacks.Algebraization.pullbackSheafHomMap_factor`, on the canonical image along `g` of a local
section `s` of `ℋom(b^* 𝒢, b^* ℱ)` and the canonical image along `g ≫ b` of a local section `m` of
`𝒢`: the comparison for `g` is computed on canonical images by
`Stacks.Algebraization.pullbackSheafHomMap_unit_eval`, and the two conjugating isomorphisms are
moved past it by `Stacks.Algebraization.pullbackObjFactorIso_inv_unit`. -/
private theorem conj_unit_eval {Z A B : Scheme.{u}} (G F : Z.Modules) (b : B ⟶ Z) (g : A ⟶ B)
    (U : Z.Opens)
    (s : ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
      ((Scheme.Modules.pullback b).obj F)).val.obj (op (b ⁻¹ᵁ U))) (m : Γ(G, U)) :
    (((sheafHomConj (pullbackObjFactorIso G g (rfl : g ≫ b = g ≫ b)).inv
              (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom).val.app
            (op ((g ≫ b) ⁻¹ᵁ U))
          ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
                ((Scheme.Modules.pullback b).obj F)).val.app (op ((g ≫ b) ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
                ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
                  ((Scheme.Modules.pullback b).obj F))).val.app (op (b ⁻¹ᵁ U)) s))).app
        (op (Over.mk (𝟙 ((g ≫ b) ⁻¹ᵁ U))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app G).val.app (op U) m) =
      (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom.val.app (op ((g ≫ b) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pullback b).obj F)).val.app (op (b ⁻¹ᵁ U))
          ((s.app (op (Over.mk (𝟙 (b ⁻¹ᵁ U))))).hom
            (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app G).val.app
              (op U) m))) := by
  refine Eq.trans (sheafHomConj_app_apply _ _ ((g ≫ b) ⁻¹ᵁ U) _
    (Over.mk (𝟙 ((g ≫ b) ⁻¹ᵁ U))) _) ?_
  refine congrArg (fun z => (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom.val.app
    (op ((g ≫ b) ⁻¹ᵁ U)) z) ?_
  refine Eq.trans (congrArg (fun z => (((pullbackSheafHomMap g
        ((Scheme.Modules.pullback b).obj G) ((Scheme.Modules.pullback b).obj F)).val.app
          (op ((g ≫ b) ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
                ((Scheme.Modules.pullback b).obj F))).val.app (op (b ⁻¹ᵁ U)) s)).app
        (op (Over.mk (𝟙 ((g ≫ b) ⁻¹ᵁ U))))).hom z)
    (pullbackObjFactorIso_inv_unit G b g U m)) ?_
  exact pullbackSheafHomMap_unit_eval g ((Scheme.Modules.pullback b).obj G)
    ((Scheme.Modules.pullback b).obj F) (b ⁻¹ᵁ U) s
    (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app G).val.app (op U) m)

/-- The whole composite of `Stacks.Algebraization.pullbackSheafHomMap_factor`, on the canonical
image of a local section `t` of `ℋom(𝒢, ℱ)` and of a local section `m` of `𝒢`: it is the canonical
image of the value `t(m)`, which is also what the comparison attached to `g ≫ b` gives. -/
private theorem factor_eval {Z A B : Scheme.{u}} (G F : Z.Modules) (b : B ⟶ Z) (g : A ⟶ B)
    (U : Z.Opens) (t : ((sheafHomFunctor Z G).obj F).val.obj (op U)) (m : Γ(G, U)) :
    (((sheafHomConj (pullbackObjFactorIso G g (rfl : g ≫ b = g ≫ b)).inv
              (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom).val.app
            (op ((g ≫ b) ⁻¹ᵁ U))
          ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
                ((Scheme.Modules.pullback b).obj F)).val.app (op ((g ≫ b) ⁻¹ᵁ U))
            (((Scheme.Modules.pullback g).map (pullbackSheafHomMap b G F)).val.app
                (op ((g ≫ b) ⁻¹ᵁ U))
              ((pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g
                    (rfl : g ≫ b = g ≫ b)).inv.val.app (op ((g ≫ b) ⁻¹ᵁ U))
                (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app
                  ((sheafHomFunctor Z G).obj F)).val.app (op U) t))))).app
        (op (Over.mk (𝟙 ((g ≫ b) ⁻¹ᵁ U))))).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app G).val.app (op U) m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app F).val.app (op U)
        ((t.app (op (Over.mk (𝟙 U)))).hom m) := by
  have hE : ((Scheme.Modules.pullback g).map (pullbackSheafHomMap b G F)).val.app
        (op ((g ≫ b) ⁻¹ᵁ U))
        ((pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g
              (rfl : g ≫ b = g ≫ b)).inv.val.app (op ((g ≫ b) ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app
            ((sheafHomFunctor Z G).obj F)).val.app (op U) t)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
              ((Scheme.Modules.pullback b).obj F))).val.app (op (b ⁻¹ᵁ U))
        ((pullbackSheafHomMap b G F).val.app (op (b ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
            ((sheafHomFunctor Z G).obj F)).val.app (op U) t)) := by
    refine Eq.trans (congrArg (fun z => ((Scheme.Modules.pullback g).map
      (pullbackSheafHomMap b G F)).val.app (op ((g ≫ b) ⁻¹ᵁ U)) z)
      (pullbackObjFactorIso_inv_unit ((sheafHomFunctor Z G).obj F) b g U t)) ?_
    exact Stacks.Chow.pullback_map_unit_app g (pullbackSheafHomMap b G F) (b ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
        ((sheafHomFunctor Z G).obj F)).val.app (op U) t)
  refine Eq.trans (congrArg (fun z => (((sheafHomConj
        (pullbackObjFactorIso G g (rfl : g ≫ b = g ≫ b)).inv
        (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom).val.app (op ((g ≫ b) ⁻¹ᵁ U))
        ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
          ((Scheme.Modules.pullback b).obj F)).val.app (op ((g ≫ b) ⁻¹ᵁ U)) z)).app
      (op (Over.mk (𝟙 ((g ≫ b) ⁻¹ᵁ U))))).hom
      (((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ b)).unit.app G).val.app (op U) m))
    hE) ?_
  refine (conj_unit_eval G F b g U ((pullbackSheafHomMap b G F).val.app (op (b ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app
      ((sheafHomFunctor Z G).obj F)).val.app (op U) t)) m).trans ?_
  refine Eq.trans (congrArg (fun z =>
      (pullbackObjFactorIso F g (rfl : g ≫ b = g ≫ b)).hom.val.app (op ((g ≫ b) ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback b).obj F)).val.app (op (b ⁻¹ᵁ U)) z))
    (pullbackSheafHomMap_unit_eval b G F U t m)) ?_
  exact pullbackObjFactorIso_hom_unit F b g U ((t.app (op (Over.mk (𝟙 U)))).hom m)

/-- **The canonical comparison of [Stacks, Tag 0GMX] is natural in the morphism of schemes.**
For a factorization `g ≫ b = a` the comparison
`a^* ℋom(𝒢, ℱ) ⟶ ℋom(a^* 𝒢, a^* ℱ)` is the pullback along `g` of the comparison for `b`, followed
by the comparison for `g` at the two pulled-back modules, followed by the conjugation by the
identifications `g^* b^* 𝒢 ≅ a^* 𝒢` and `g^* b^* ℱ ≅ a^* ℱ`, and preceded by the identification
`g^* b^* ℋom(𝒢, ℱ) ≅ a^* ℋom(𝒢, ℱ)`.

Both sides are morphisms out of `a^* ℋom(𝒢, ℱ)` into `ℋom(a^* 𝒢, a^* ℱ)`, so
`Stacks.Algebraization.hom_ext_sheafHom_pullback` reduces the identity to the canonical images of
a local section of `ℋom(𝒢, ℱ)` and of a local section of `𝒢`, where both sides take the canonical
image of the value of the first on the second. -/
public theorem pullbackSheafHomMap_factor {Z : Scheme.{u}} (G F : Z.Modules) {A B : Scheme.{u}}
    {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a) :
    pullbackSheafHomMap a G F =
      (pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g hg).inv ≫
        (Scheme.Modules.pullback g).map (pullbackSheafHomMap b G F) ≫
          pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
              ((Scheme.Modules.pullback b).obj F) ≫
            sheafHomConj (pullbackObjFactorIso G g hg).inv
              (pullbackObjFactorIso F g hg).hom := by
  subst hg
  refine hom_ext_sheafHom_pullback (g ≫ b) ((sheafHomFunctor Z G).obj F) G (fun U t m => ?_)
  exact (pullbackSheafHomMap_unit_eval (g ≫ b) G F U t m).trans
    (factor_eval G F b g U t m).symm

/-- **The morphism between the pullbacks attached to a global section of `f^* ℋom(𝒢, ℱ)`**: the
canonical comparison of [Stacks, Tag 0GMX] on global sections, followed by the identification
`Stacks.Algebraization.internalHomSectionsTopEquiv` of the global sections of an internal hom with
the morphisms. This is the family conditions (3) and (4) of [Stacks, Tag 0EK2] are compared
through. -/
public def pullbackSheafHomSection {Z : Scheme.{u}} (G F : Z.Modules) {A : Scheme.{u}}
    (f : A ⟶ Z)
    (x : Γ((Scheme.Modules.pullback f).obj ((sheafHomFunctor Z G).obj F), (⊤ : A.Opens))) :
    (Scheme.Modules.pullback f).obj G ⟶ (Scheme.Modules.pullback f).obj F :=
  internalHomSectionsTopEquiv ((Scheme.Modules.pullback f).obj G)
    ((Scheme.Modules.pullback f).obj F)
    ((pullbackSheafHomMap f G F).val.app (op (⊤ : A.Opens)) x)

/-- **The family is natural in the morphism.** For a factorization `g ≫ b = a`, the morphism
`a^* 𝒢 ⟶ a^* ℱ` attached to the pullback along `g` of a global section of `b^* ℋom(𝒢, ℱ)` is the
transport along `Stacks.Algebraization.pullbackHomMap` of the morphism `b^* 𝒢 ⟶ b^* ℱ` attached to
that section. This is the one property of the family the three compatibilities of condition (4)
are read off, and it is `Stacks.Algebraization.pullbackSheafHomMap_factor` on global sections,
together with the characterisation
`Stacks.Algebraization.pullbackSheafHomMap_app_top` of the comparison on the canonical image of a
global section. -/
public theorem pullbackSheafHomSection_factor {Z : Scheme.{u}} (G F : Z.Modules)
    {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
    (x : Γ((Scheme.Modules.pullback b).obj ((sheafHomFunctor Z G).obj F), (⊤ : B.Opens))) :
    pullbackSheafHomSection G F a
        ((pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g hg).hom.app ⊤
          (pullbackGlobalSections g
            ((Scheme.Modules.pullback b).obj ((sheafHomFunctor Z G).obj F)) x)) =
      pullbackHomMap G F g hg (pullbackSheafHomSection G F b x) := by
  have hnat : ((Scheme.Modules.pullback g).map (pullbackSheafHomMap b G F)).app ⊤
        (pullbackGlobalSections g
          ((Scheme.Modules.pullback b).obj ((sheafHomFunctor Z G).obj F)) x) =
      pullbackGlobalSections g
          ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
            ((Scheme.Modules.pullback b).obj F))
        ((pullbackSheafHomMap b G F).app (⊤ : B.Opens) x) :=
    (pullbackGlobalSections_natural g (pullbackSheafHomMap b G F) x).symm
  have hstep : (pullbackSheafHomMap a G F).app (⊤ : A.Opens)
        ((pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g hg).hom.app ⊤
          (pullbackGlobalSections g
            ((Scheme.Modules.pullback b).obj ((sheafHomFunctor Z G).obj F)) x)) =
      (sheafHomConj (pullbackObjFactorIso G g hg).inv
            (pullbackObjFactorIso F g hg).hom).app (⊤ : A.Opens)
        ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
              ((Scheme.Modules.pullback b).obj F)).app ⊤
          (pullbackGlobalSections g
              ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
                ((Scheme.Modules.pullback b).obj F))
            ((pullbackSheafHomMap b G F).app (⊤ : B.Opens) x))) := by
    refine Eq.trans (ConcreteCategory.congr_hom
      (congrArg (fun χ => Scheme.Modules.Hom.app χ (⊤ : A.Opens))
        (pullbackSheafHomMap_factor G F g hg)) _) ?_
    refine congrArg (fun z => (sheafHomConj (pullbackObjFactorIso G g hg).inv
      (pullbackObjFactorIso F g hg).hom).app (⊤ : A.Opens)
      ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
        ((Scheme.Modules.pullback b).obj F)).app ⊤ z)) ?_
    exact (congrArg (fun z => ((Scheme.Modules.pullback g).map
      (pullbackSheafHomMap b G F)).app ⊤ z)
      (inv_app_hom_app (pullbackObjFactorIso ((sheafHomFunctor Z G).obj F) g hg) ⊤ _)).trans hnat
  refine Eq.trans (congrArg (fun z => internalHomSectionsTopEquiv
    ((Scheme.Modules.pullback a).obj G) ((Scheme.Modules.pullback a).obj F) z) hstep) ?_
  refine Eq.trans (internalHomSectionsTopEquiv_sheafHomConj
    (pullbackObjFactorIso G g hg).inv (pullbackObjFactorIso F g hg).hom _) ?_
  refine congrArg (fun ψ => (pullbackObjFactorIso G g hg).inv ≫ ψ ≫
    (pullbackObjFactorIso F g hg).hom) ?_
  refine Eq.trans (congrArg (fun z => internalHomSectionsTopEquiv
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj G))
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj F))
      ((pullbackSheafHomMap g ((Scheme.Modules.pullback b).obj G)
          ((Scheme.Modules.pullback b).obj F)).app ⊤
        (pullbackGlobalSections g
          ((sheafHomFunctor B ((Scheme.Modules.pullback b).obj G)).obj
            ((Scheme.Modules.pullback b).obj F)) z)))
    ((internalHomSectionsTopEquiv ((Scheme.Modules.pullback b).obj G)
      ((Scheme.Modules.pullback b).obj F)).symm_apply_apply
        ((pullbackSheafHomMap b G F).app (⊤ : B.Opens) x)).symm) ?_
  exact pullbackSheafHomMap_app_top g ((Scheme.Modules.pullback b).obj G)
    ((Scheme.Modules.pullback b).obj F)
    (internalHomSectionsTopEquiv ((Scheme.Modules.pullback b).obj G)
      ((Scheme.Modules.pullback b).obj F) ((pullbackSheafHomMap b G F).app (⊤ : B.Opens) x))

/-- **The family is bijective as soon as the canonical comparison is invertible.** It is then the
composite of two bijections: the components of an isomorphism of modules are bijective, and the
global sections of an internal hom are the morphisms. -/
public theorem bijective_pullbackSheafHomSection {Z : Scheme.{u}} (G F : Z.Modules)
    {A : Scheme.{u}} (f : A ⟶ Z) [IsIso (pullbackSheafHomMap f G F)] :
    Function.Bijective (pullbackSheafHomSection G F f) :=
  (internalHomSectionsTopEquiv ((Scheme.Modules.pullback f).obj G)
      ((Scheme.Modules.pullback f).obj F)).toEquiv.bijective.comp
    (bijective_app_of_isIso (pullbackSheafHomMap f G F) ⊤)

namespace InfinitesimalTower

variable {Z : Scheme.{u}} (T : InfinitesimalTower Z)

/-- **Condition (3) for `E` gives condition (4) for `(G, F)` as soon as the global sections of
the pullbacks of `E` are the morphisms between the pullbacks of `G` and of `F`.** -/
public theorem isHomsComplete_of_isSectionsComplete_of_homEquiv (E G F : Z.Modules)
    (β : ∀ {A : Scheme.{u}} (f : A ⟶ Z),
      Γ((Scheme.Modules.pullback f).obj E, (⊤ : A.Opens)) →
        ((Scheme.Modules.pullback f).obj G ⟶ (Scheme.Modules.pullback f).obj F))
    (hβ : ∀ {A : Scheme.{u}} (f : A ⟶ Z), Function.Bijective (β f))
    (hβnat : ∀ {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
      (x : Γ((Scheme.Modules.pullback b).obj E, (⊤ : B.Opens))),
      β a ((pullbackObjFactorIso E g hg).hom.app ⊤
          (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj E) x)) =
        pullbackHomMap G F g hg (β b x))
    (hE : T.IsSectionsComplete E) : T.IsHomsComplete G F :=
  T.isHomsComplete_of_isSectionsComplete E G F
    (fun W _ t => β W.ι (pullbackSectionsAt W.ι E W.ι_preimage_self t))
    (fun W _ => (hβ W.ι).comp (bijective_pullbackSectionsAt_ι W E W.ι_preimage_self))
    (fun W W' _ _ h t => by
      have haV : W'.ι ⁻¹ᵁ W = ⊤ :=
        le_antisymm le_top (le_trans W'.ι_preimage_self.ge
          (leOfHom ((Opens.map W'.ι.base).map (homOfLE h))))
      refine Eq.trans (congrArg (β W'.ι)
        ((pullbackSectionsAt_restrict W'.ι E h haV W'.ι_preimage_self t).trans
          (pullbackSectionsAt_factor E (Z.homOfLE h) (Z.homOfLE_ι h)
            W.ι_preimage_self haV t).symm)) ?_
      exact hβnat (Z.homOfLE h) (Z.homOfLE_ι h) _)
    (fun n => β (T.obj n).hom) (fun n => hβ (T.obj n).hom)
    (fun n m h x =>
      (congrArg (β (T.obj n).hom)
        (pullbackSectionsMap_apply_factor E (T.trans n m h) x)).trans
          (hβnat (T.trans n m h).left (Over.w (T.trans n m h)) x))
    (fun W hW n t =>
      (congrArg (β (T.obj n).hom)
        (pullbackSectionsAt_factor E (T.homToOpen hW n) (T.homToOpen_ι hW n)
          W.ι_preimage_self (T.preimage_eq_top hW n) t).symm).trans
          (hβnat (T.homToOpen hW n) (T.homToOpen_ι hW n) _))
    hE

/-- **The implication (3) ⇒ (4) of [Stacks, Tag 0EK2] for an abstract tower, granted that the
comparison of [Stacks, Tag 0GMX] is invertible.** Condition (3) for the internal hom
`ℋom(𝒢, ℱ)` is condition (4) for the pair `(𝒢, ℱ)`: the sections of `ℋom(𝒢, ℱ)` over an open
neighbourhood `W` of the support are the morphisms `𝒢|_W ⟶ ℱ|_W`, its global sections on the
`n`-th term of the tower are the morphisms `𝒢|_{Y_n} ⟶ ℱ|_{Y_n}`, and both identifications are
instances of the one family `Stacks.Algebraization.pullbackSheafHomSection`, whose naturality
`Stacks.Algebraization.pullbackSheafHomSection_factor` supplies the three compatibilities. -/
public theorem IsHomsComplete.of_isSectionsComplete_sheafHom_of_isIso (G F : Z.Modules)
    (hiso : ∀ {A : Scheme.{u}} (f : A ⟶ Z), IsIso (pullbackSheafHomMap f G F))
    (h : T.IsSectionsComplete ((sheafHomFunctor Z G).obj F)) : T.IsHomsComplete G F :=
  T.isHomsComplete_of_isSectionsComplete_of_homEquiv ((sheafHomFunctor Z G).obj F) G F
    (fun f => pullbackSheafHomSection G F f)
    (fun f => have := hiso f; bijective_pullbackSheafHomSection G F f)
    (fun g hg x => pullbackSheafHomSection_factor G F g hg x) h

/-- **The implication (3) ⇒ (4) of [Stacks, Tag 0EK2] for an abstract tower and a finite locally
free `𝒢`, granted the identification of the two comparisons.** The hypothesis `hid` says that the
isomorphism `Stacks.Algebraization.pullbackSheafHomIso` — which exists for `𝒢` finite locally
free, by the rank-one description `ℋom(𝒢, ℱ) ≅ ℱ ⊗ 𝒢^∨` — *is* the canonical comparison
`Stacks.Algebraization.pullbackSheafHomMap` of [Stacks, Tag 0GMX]. That identification is the one
statement of this circle of ideas the library does not have; the implementation notes say what
proving it needs. Everything else is proved here. -/
public theorem IsHomsComplete.of_isSectionsComplete_sheafHom (G F : Z.Modules)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (hid : ∀ {A : Scheme.{u}} (f : A ⟶ Z),
      (pullbackSheafHomIso f G F hG).hom = pullbackSheafHomMap f G F)
    (h : T.IsSectionsComplete ((sheafHomFunctor Z G).obj F)) : T.IsHomsComplete G F :=
  IsHomsComplete.of_isSectionsComplete_sheafHom_of_isIso T G F
    (fun f => by rw [← hid f]; infer_instance) h

end InfinitesimalTower

end Stacks.Algebraization

end
