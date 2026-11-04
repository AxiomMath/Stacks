module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsAtFactor

/-!
# Condition (4) at the structure sheaf is condition (3)

Condition (3) of [Stacks, Tag 0EK2] compares the colimit of the sections `Γ(W, ℰ)` over the open
neighbourhoods `W` of a closed subscheme with the inverse limit of the sections `Γ(Y_n, ℰ|_{Y_n})`
on its infinitesimal neighbourhoods; condition (4) compares, for two modules `𝒢` and `ℱ`, the
colimit of the morphisms `𝒢|_W ⟶ ℱ|_W` with the inverse limit of the morphisms
`𝒢|_{Y_n} ⟶ ℱ|_{Y_n}`. Taking `𝒢 = 𝒪` turns the second comparison into the first, because a
morphism out of the structure sheaf is a section. This file carries that out, and so proves the
implication `(4) ⇒ (3)`, whose proof the source omits.

The identification is built from the pullback--pushforward adjunction rather than from an
identification `g^* 𝒪_Z ≅ 𝒪_A` of structure sheaves: for a morphism of schemes `g : A ⟶ Z` and a
module `M` on `A`,

`(g^* 𝒪_Z ⟶ M) ≃ (𝒪_Z ⟶ g_* M) ≃ (g_* M).sections ≃ Γ(g_* M, ⊤) = Γ(M, ⊤)`,

the middle bijection being `SheafOfModules.unitHomEquiv` and the last two equalities holding
because `⊤` is terminal in the site of opens and `g ⁻¹ᵁ ⊤ = ⊤`. Read through this bijection, a
morphism `φ` is evaluation at the *unit section* of `g^* 𝒪_Z`, the image of `1 ∈ Γ(Z, ⊤)` under
`AlgebraicGeometry.pullbackGlobalSections`; everything else follows from the functoriality of that
map.

## Main definitions

* `Stacks.Algebraization.unitPullbackHomEquiv` — a morphism from the pullback of the structure
  sheaf to a module is a global section of that module.
* `Stacks.Algebraization.unitSection` — the unit section of the pullback of the structure sheaf.
* `Stacks.Algebraization.InfinitesimalTower.unitHomOn` and
  `Stacks.Algebraization.InfinitesimalTower.unitHomAt` — the two identifications of condition (3)
  with condition (4) at the structure sheaf: of the sections over an open containing the support
  with the morphisms `𝒪|_W ⟶ ℰ|_W`, and of the sections on the `n`-th term of the tower with the
  morphisms `𝒪|_{Y_n} ⟶ ℰ|_{Y_n}`.

## Main results

* `Stacks.Algebraization.unitPullbackHomEquiv_pullbackHomMap` — the comparison map
  `Stacks.Algebraization.pullbackHomMap` on morphisms out of the structure sheaf is, under the
  identification above, the comparison map on global sections.
* `Stacks.Algebraization.InfinitesimalTower.unitHomAt_sectionsAt`,
  `Stacks.Algebraization.InfinitesimalTower.unitHomOn_restrict` and
  `Stacks.Algebraization.InfinitesimalTower.unitHomAt_trans` — the three compatibilities the
  identification has to satisfy: with the comparison of the tower, with shrinking the open, and
  with the transition maps of the inverse system.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.of_isHomsComplete_unit` —
  **the implication (4) ⇒ (3) of [Stacks, Tag 0EK2]** for an abstract tower: condition (4) for the
  pair `(𝒪_Z, ℰ)` is condition (3) for `ℰ`.
* `Stacks.Algebraization.InfinitesimalTower.IsSectionsComplete.isHomsComplete_unit` — the
  converse, which the same data gives for free.

The attribute for Tag 0EK2 sits on
`Stacks.Algebraization.Tag0EK2.tfae_completion_fully_faithful_on_neighbourhoods`, which states the
whole tag; these are two of the implications it is assembled from, and carry no attribute of their
own. They are stated for an abstract `Stacks.Algebraization.InfinitesimalTower`, so that
instantiating them at the tower of infinitesimal neighbourhoods read over a neighbourhood is a
substitution.

## Implementation notes

The whole bookkeeping is routed through
`Stacks.Algebraization.InfinitesimalTower.isSectionsComplete_of_isHomsComplete` and its converse:
the only mathematical content owed here is the data of the two identifications, their bijectivity
and the three compatibilities. Bijectivity on the colimit side is
`Stacks.Algebraization.bijective_pullbackSectionsAt_ι` — that the sections of `ℰ` over `W` are the
global sections of `ℰ|_W` — and on the limit side it is automatic, the identification being an
`Equiv`. Each of the three compatibilities is the master lemma
`unitPullbackHomEquiv_pullbackHomMap` followed by one statement about the comparison on global
sections, so the three proofs have the same five-step shape.

Two performance hazards shape the phrasing, both of them about
`AlgebraicGeometry.Scheme.Modules.pullback`, which is built from a sheafification. Morphisms are
written out with a factorization equation supplied, never as morphisms of `CategoryTheory.Over Z`,
because deciding `(Over.mk f).hom =?= f` inside the argument of that functor exhausts the
elaborator; this is the phrasing `TowerHoms.lean` already uses, and the one place a morphism of
`Over Z` does occur — the transition of a tower — it is consumed through `CategoryTheory.Over.w`.
And `rw` cannot cross the semireducible projection separating `Γ(M, U)` from a presheaf's
sections, so the proofs are in term mode throughout: `Eq.trans`, `congrArg`,
`CategoryTheory.NatTrans.naturality_apply` and `CategoryTheory.ConcreteCategory.congr_hom` in
place of rewrites.

Three transports along `f ⁻¹ᵁ ⊤ = ⊤` occur, in `AlgebraicGeometry.pullbackGlobalSections` and in
`AlgebraicGeometry.pullbackSectionsMap`. They are all the identity, but not definitionally: the
equation is a `Prop`, so `eqToHom` of it is definitionally `eqToHom rfl`, yet `F.map (𝟙 _) = 𝟙 _`
is a functor law and not a reduction. `pullback_presheaf_mapTop_id` discharges them, using that
the homs of `Opens` are a subsingleton; the same subsingleton argument identifies the two
transports along `(g ≫ b) ⁻¹ᵁ V = ⊤` that appear in `pullbackSectionsAt_factor`.

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

variable {Z : Scheme.{u}}

/-! ### A morphism out of the structure sheaf is a global section -/

/-- The sections of an `𝒪_Z`-module — a restriction-compatible family of sections over every open
— are its sections over `⊤`, because `⊤` is terminal in the site of opens of `Z`. -/
public def sectionsTopEquiv (M : Z.Modules) : M.sections ≃ Γ(M, (⊤ : Z.Opens)) :=
  Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M Limits.isTerminalTop

/-- **A morphism out of the structure sheaf is a global section.** This is
`SheafOfModules.unitHomEquiv` with the sections of a module read over `⊤`. -/
public def unitHomEquivTop (M : Z.Modules) :
    (SheafOfModules.unit Z.ringCatSheaf ⟶ M) ≃ Γ(M, (⊤ : Z.Opens)) :=
  (SheafOfModules.unitHomEquiv M).trans (sectionsTopEquiv M)

/-- The global section a morphism out of the structure sheaf names is the image of the unit of
`Γ(Z, ⊤)`. -/
public theorem unitHomEquivTop_apply (M : Z.Modules)
    (φ : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    unitHomEquivTop M φ = Scheme.Modules.Hom.app φ ⊤ (1 : Γ(Z, (⊤ : Z.Opens))) := rfl

/-- **A morphism from the pullback of the structure sheaf along `g` to a module `M` on the source
is a global section of `M`.** The pullback--pushforward adjunction turns it into a morphism out of
the structure sheaf of the target, which `unitHomEquivTop` turns into a section of `g_* M` over
`⊤`; that is a section of `M` over `g ⁻¹ᵁ ⊤ = ⊤`. -/
public def unitPullbackHomEquiv {A : Scheme.{u}} (g : A ⟶ Z) (M : A.Modules) :
    ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶ M) ≃
      Γ(M, (⊤ : A.Opens)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ M).trans
    (unitHomEquivTop ((Scheme.Modules.pushforward g).obj M))

/-- The unit section of the pullback of the structure sheaf along `g`: the global section of
`g^* 𝒪_Z` named by the identity morphism, equivalently the pullback of `1 ∈ Γ(Z, ⊤)`. -/
public def unitSection {A : Scheme.{u}} (g : A ⟶ Z) :
    Γ((Scheme.Modules.pullback g).obj (SheafOfModules.unit Z.ringCatSheaf), (⊤ : A.Opens)) :=
  Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
    (SheafOfModules.unit Z.ringCatSheaf)) ⊤ (1 : Γ(Z, (⊤ : Z.Opens)))

/-- The unit section is the pullback of the unit of `Γ(Z, ⊤)` on global sections. -/
public theorem unitSection_eq {A : Scheme.{u}} (g : A ⟶ Z) :
    unitSection g =
      pullbackGlobalSections g (SheafOfModules.unit Z.ringCatSheaf)
        (1 : Γ(Z, (⊤ : Z.Opens))) :=
  (ConcreteCategory.congr_hom
    (pullbackGlobalSections_eq_unit g (SheafOfModules.unit Z.ringCatSheaf)) _).symm

/-- The global section a morphism out of the pulled-back structure sheaf names is its value at
the unit section. -/
public theorem unitPullbackHomEquiv_apply {A : Scheme.{u}} (g : A ⟶ Z) (M : A.Modules)
    (φ : (Scheme.Modules.pullback g).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶ M) :
    unitPullbackHomEquiv g M φ = Scheme.Modules.Hom.app φ ⊤ (unitSection g) := rfl

/-! ### The comparison map on morphisms is the comparison map on sections -/

/-- **Functoriality of the pullback map on global sections against a factorization.** For
`g ≫ b = a`, pulling a global section back along `b` and then along `g` and applying the
identification `g^* b^* M ≅ a^* M` is pulling it back along `a`. -/
public theorem pullbackObjFactorIso_pullbackGlobalSections (M : Z.Modules)
    {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
    (y : Γ(M, (⊤ : Z.Opens))) :
    (pullbackObjFactorIso M g hg).hom.app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj M)
          (pullbackGlobalSections b M y)) =
      pullbackGlobalSections a M y := by
  subst hg
  have h := ConcreteCategory.congr_hom (pullbackGlobalSections_comp_hom g b M) y
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- The unit sections of the pullbacks of the structure sheaf along `a` and along `b` correspond
under the identification `g^* b^* 𝒪_Z ≅ a^* 𝒪_Z` attached to a factorization `g ≫ b = a`. This is
the previous lemma at the structure sheaf and the unit section. -/
public theorem unitSection_pullbackObjFactorIso {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z}
    (g : A ⟶ B) (hg : g ≫ b = a) :
    (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).inv.app ⊤ (unitSection a) =
      pullbackGlobalSections g
        ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
        (unitSection b) := by
  have h1 : (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).hom.app ⊤
        (pullbackGlobalSections g
          ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
          (unitSection b)) =
      unitSection a :=
    (congrArg (fun y => (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).hom.app ⊤
        (pullbackGlobalSections g
          ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf)) y))
      (unitSection_eq b)).trans
      ((pullbackObjFactorIso_pullbackGlobalSections (SheafOfModules.unit Z.ringCatSheaf) g hg
        (1 : Γ(Z, (⊤ : Z.Opens)))).trans (unitSection_eq a).symm)
  have h2 : (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).inv.app ⊤
        ((pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).hom.app ⊤
          (pullbackGlobalSections g
            ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
            (unitSection b))) =
      pullbackGlobalSections g
        ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
        (unitSection b) :=
    congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤
        (pullbackGlobalSections g
          ((Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf))
          (unitSection b)))
      (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).hom_inv_id
  exact (congrArg (fun y =>
    (pullbackObjFactorIso (SheafOfModules.unit Z.ringCatSheaf) g hg).inv.app ⊤ y) h1).symm.trans h2

/-- **The master lemma: the comparison map on morphisms out of the structure sheaf is the
comparison map on global sections.** Under the identification `unitPullbackHomEquiv` of a morphism
`b^* 𝒪_Z ⟶ b^* ℰ` with a global section of `b^* ℰ`, the map `pullbackHomMap` attached to a
factorization `g ≫ b = a` becomes the pullback map on global sections along `g`, followed by the
identification `g^* b^* ℰ ≅ a^* ℰ`. -/
public theorem unitPullbackHomEquiv_pullbackHomMap (E : Z.Modules)
    {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
    (φ : (Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback b).obj E) :
    unitPullbackHomEquiv a ((Scheme.Modules.pullback a).obj E)
        (pullbackHomMap (SheafOfModules.unit Z.ringCatSheaf) E g hg φ) =
      (pullbackObjFactorIso E g hg).hom.app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj E)
          (unitPullbackHomEquiv b ((Scheme.Modules.pullback b).obj E) φ)) :=
  (congrArg (fun z => Scheme.Modules.Hom.app (pullbackObjFactorIso E g hg).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map φ) ⊤ z))
      (unitSection_pullbackObjFactorIso g hg)).trans
    (congrArg (fun z => Scheme.Modules.Hom.app (pullbackObjFactorIso E g hg).hom ⊤ z)
      (pullbackGlobalSections_natural g φ (unitSection b)).symm)

/-! ### The comparison map on global sections against restriction -/

/-- The transport along `f ⁻¹ᵁ ⊤ = ⊤` occurring in `AlgebraicGeometry.pullbackGlobalSections` and
in `AlgebraicGeometry.pullbackSectionsMap` is the identity. The two opens are definitionally
equal, so the two homs between them agree — the homs of `Opens` being a subsingleton — but the
functor law has still to be invoked. -/
public theorem pullback_presheaf_mapTop_id {A B : Scheme.{u}} (f : A ⟶ B) (M : B.Modules) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom (by simp : (⊤ : A.Opens) = f ⁻¹ᵁ (⊤ : B.Opens))).op =
      𝟙 Γ((Scheme.Modules.pullback f).obj M, (⊤ : A.Opens)) := by
  have h0 : (eqToHom (by simp : (⊤ : A.Opens) = f ⁻¹ᵁ (⊤ : B.Opens))).op =
      𝟙 (op (f ⁻¹ᵁ (⊤ : B.Opens))) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  exact (congrArg ((Scheme.Modules.pullback f).obj M).presheaf.map h0).trans
    (((Scheme.Modules.pullback f).obj M).presheaf.map_id _)

/-- **The transition map of the inverse system of global sections, read off its definition.**
`AlgebraicGeometry.pullbackSectionsMap` along a morphism of schemes over `S` is the pullback map on
global sections along the underlying morphism, followed by the identification of iterated
pullbacks. -/
public theorem pullbackSectionsMap_eq_pullbackGlobalSections {S : Scheme.{u}} (F : S.Modules)
    {X Y : Over S} (g : X ⟶ Y)
    (x : Γ((Scheme.Modules.pullback Y.hom).obj F, (⊤ : Y.left.Opens))) :
    pullbackSectionsMap F g x =
      (pullbackObjFactorIso F g.left (Over.w g)).hom.app ⊤
        (pullbackGlobalSections g.left ((Scheme.Modules.pullback Y.hom).obj F) x) := by
  have hdef : pullbackSectionsMap F g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback Y.hom).obj F) ≫
          (Scheme.Modules.pushforward g.left).map
            (pullbackObjFactorIso F g.left (Over.w g)).hom).app ⊤ ≫
        ((Scheme.Modules.pullback X.hom).obj F).presheaf.map
          (eqToHom (show (⊤ : X.left.Opens) = g.left ⁻¹ᵁ (⊤ : Y.left.Opens) by simp)).op := rfl
  have hid := pullback_presheaf_mapTop_id X.hom F
  have hstep : pullbackSectionsMap F g =
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
          ((Scheme.Modules.pullback Y.hom).obj F) ≫
        (Scheme.Modules.pushforward g.left).map
          (pullbackObjFactorIso F g.left (Over.w g)).hom).app ⊤ :=
    hdef.trans ((congrArg (fun ψ =>
      ((Scheme.Modules.pullbackPushforwardAdjunction g.left).unit.app
            ((Scheme.Modules.pullback Y.hom).obj F) ≫
          (Scheme.Modules.pushforward g.left).map
            (pullbackObjFactorIso F g.left (Over.w g)).hom).app ⊤ ≫ ψ) hid).trans
      (Category.comp_id _))
  exact (ConcreteCategory.congr_hom hstep x).trans
    (congrArg (fun y => Scheme.Modules.Hom.app (pullbackObjFactorIso F g.left (Over.w g)).hom ⊤ y)
      (ConcreteCategory.congr_hom
        (pullbackGlobalSections_eq_unit g.left ((Scheme.Modules.pullback Y.hom).obj F)) x).symm)

/-- A morphism `ψ : a^* 𝒪_Z ⟶ a^* ℰ` is the `pullbackHomMap` of `φ` along a factorization
`g ≫ b = a` as soon as its global section is the transport of that of `φ`. -/
private theorem eq_pullbackHomMap_of_apply (E : Z.Modules)
    {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)
    (φ : (Scheme.Modules.pullback b).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback b).obj E)
    (ψ : (Scheme.Modules.pullback a).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback a).obj E)
    (s : Γ((Scheme.Modules.pullback b).obj E, (⊤ : B.Opens)))
    (hs : unitPullbackHomEquiv b ((Scheme.Modules.pullback b).obj E) φ = s)
    (hψ : unitPullbackHomEquiv a ((Scheme.Modules.pullback a).obj E) ψ =
      (pullbackObjFactorIso E g hg).hom.app ⊤
        (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj E) s)) :
    ψ = pullbackHomMap (SheafOfModules.unit Z.ringCatSheaf) E g hg φ :=
  (unitPullbackHomEquiv a ((Scheme.Modules.pullback a).obj E)).injective
    (hψ.trans ((congrArg (fun y => (pullbackObjFactorIso E g hg).hom.app ⊤
      (pullbackGlobalSections g ((Scheme.Modules.pullback b).obj E) y)) hs).symm.trans
      (unitPullbackHomEquiv_pullbackHomMap E g hg φ).symm))

namespace InfinitesimalTower

variable (T : InfinitesimalTower Z) (E : Z.Modules)

/-! ### The identification of condition (3) with condition (4) at the structure sheaf -/

/-- **The colimit-side identification.** A section of `ℰ` over an open `W` is a morphism
`𝒪_Z|_W ⟶ ℰ|_W`: the section determines a global section of `ℰ|_W`, which `unitPullbackHomEquiv`
turns into such a morphism. -/
public def unitHomOn (W : Z.Opens) (t : Γ(E, W)) :
    (Scheme.Modules.pullback W.ι).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback W.ι).obj E :=
  (unitPullbackHomEquiv W.ι ((Scheme.Modules.pullback W.ι).obj E)).symm
    (pullbackSectionsAt W.ι E W.ι_preimage_self t)

/-- **The limit-side identification.** A global section of the pullback of `ℰ` to the `n`-th term
of the tower is a morphism from the pullback of the structure sheaf to it. -/
public def unitHomAt (n : ℕ) (x : Γ((Scheme.Modules.pullback (T.obj n).hom).obj E, ⊤)) :
    (Scheme.Modules.pullback (T.obj n).hom).obj (SheafOfModules.unit Z.ringCatSheaf) ⟶
      (Scheme.Modules.pullback (T.obj n).hom).obj E :=
  (unitPullbackHomEquiv (T.obj n).hom
    ((Scheme.Modules.pullback (T.obj n).hom).obj E)).symm x

/-- The colimit-side identification is bijective: it is `unitPullbackHomEquiv` composed with the
identification of the sections of `ℰ` over `W` with the global sections of `ℰ|_W`. -/
public theorem bijective_unitHomOn (W : Z.Opens) : Function.Bijective (unitHomOn E W) :=
  (unitPullbackHomEquiv W.ι
      ((Scheme.Modules.pullback W.ι).obj E)).symm.bijective.comp
    (bijective_pullbackSectionsAt_ι W E W.ι_preimage_self)

/-- The limit-side identification is bijective, being an `Equiv`. -/
public theorem bijective_unitHomAt (n : ℕ) : Function.Bijective (T.unitHomAt E n) :=
  (unitPullbackHomEquiv (T.obj n).hom
    ((Scheme.Modules.pullback (T.obj n).hom).obj E)).symm.bijective

/-- **The two identifications intertwine the two comparisons.** The morphism
`𝒪|_{Y_n} ⟶ ℰ|_{Y_n}` named by the restriction of a section `t` of `ℰ` over `W` to the `n`-th term
of the tower is the restriction to that term of the morphism `𝒪|_W ⟶ ℰ|_W` named by `t`. -/
public theorem unitHomAt_sectionsAt {W : Z.Opens} (hW : T.support ⊆ W) (n : ℕ) (t : Γ(E, W)) :
    T.unitHomAt E n (T.sectionsAt E hW n t) =
      T.homAt (SheafOfModules.unit Z.ringCatSheaf) E hW n (unitHomOn E W t) := by
  have h1 : unitPullbackHomEquiv (T.obj n).hom ((Scheme.Modules.pullback (T.obj n).hom).obj E)
      (T.unitHomAt E n (T.sectionsAt E hW n t)) = T.sectionsAt E hW n t :=
    Equiv.apply_symm_apply _ _
  exact eq_pullbackHomMap_of_apply E (T.homToOpen hW n) (T.homToOpen_ι hW n) _ _ _
    (Equiv.apply_symm_apply _ _)
    (h1.trans (pullbackSectionsAt_factor E (T.homToOpen hW n) (T.homToOpen_ι hW n)
      W.ι_preimage_self (T.preimage_eq_top hW n) t).symm)

/-- **The colimit-side identification does not see a shrinking of the open.** The morphism named
by the restriction of a section to a smaller open is the restriction of the morphism it names. -/
public theorem unitHomOn_restrict {W W' : Z.Opens} (h : W' ≤ W) (t : Γ(E, W)) :
    unitHomOn E W' (E.presheaf.map (homOfLE h).op t) =
      homRestrict (SheafOfModules.unit Z.ringCatSheaf) E h (unitHomOn E W t) := by
  have haV : W'.ι ⁻¹ᵁ W = ⊤ :=
    le_antisymm le_top (le_trans W'.ι_preimage_self.ge
      (leOfHom ((Opens.map W'.ι.base).map (homOfLE h))))
  have h1 : unitPullbackHomEquiv W'.ι ((Scheme.Modules.pullback W'.ι).obj E)
        (unitHomOn E W' (E.presheaf.map (homOfLE h).op t)) =
      pullbackSectionsAt W'.ι E W'.ι_preimage_self (E.presheaf.map (homOfLE h).op t) :=
    Equiv.apply_symm_apply _ _
  exact eq_pullbackHomMap_of_apply E (Z.homOfLE h) (Z.homOfLE_ι h) _ _ _
    (Equiv.apply_symm_apply _ _)
    (h1.trans ((pullbackSectionsAt_restrict W'.ι E h haV W'.ι_preimage_self t).trans
      (pullbackSectionsAt_factor E (Z.homOfLE h) (Z.homOfLE_ι h) W.ι_preimage_self haV t).symm))

/-- **The limit-side identification commutes with the transition maps.** The morphism named by the
restriction of a global section from the `m`-th to the `n`-th term of the tower is the restriction
of the morphism it names. -/
public theorem unitHomAt_trans (n m : ℕ) (hnm : n ≤ m)
    (x : Γ((Scheme.Modules.pullback (T.obj m).hom).obj E, ⊤)) :
    T.unitHomAt E n (pullbackSectionsMap E (T.trans n m hnm) x) =
      T.homTrans (SheafOfModules.unit Z.ringCatSheaf) E n m hnm (T.unitHomAt E m x) := by
  have h1 : unitPullbackHomEquiv (T.obj n).hom ((Scheme.Modules.pullback (T.obj n).hom).obj E)
      (T.unitHomAt E n (pullbackSectionsMap E (T.trans n m hnm) x)) =
      pullbackSectionsMap E (T.trans n m hnm) x := Equiv.apply_symm_apply _ _
  exact eq_pullbackHomMap_of_apply E (T.trans n m hnm).left (Over.w (T.trans n m hnm)) _ _ _
    (Equiv.apply_symm_apply _ _)
    (h1.trans (pullbackSectionsMap_eq_pullbackGlobalSections E (T.trans n m hnm) x))

/-! ### The two implications -/

/-- **The implication (4) ⇒ (3) of [Stacks, Tag 0EK2]**, whose proof the source omits: condition
(4) for the pair `(𝒪_Z, ℰ)` is condition (3) for `ℰ`. A section of `ℰ` over an open containing the
support of the tower is a morphism `𝒪_Z|_W ⟶ ℰ|_W`, a global section of the pullback of `ℰ` to the
`n`-th term of the tower is a morphism out of the pullback of the structure sheaf there, and the
two identifications intertwine the comparison of condition (3) with the comparison of condition
(4). -/
public theorem IsSectionsComplete.of_isHomsComplete_unit
    (h : T.IsHomsComplete (SheafOfModules.unit Z.ringCatSheaf) E) :
    T.IsSectionsComplete E :=
  T.isSectionsComplete_of_isHomsComplete E (SheafOfModules.unit Z.ringCatSheaf) E
    (fun W _ => unitHomOn E W) (fun W _ => bijective_unitHomOn E W)
    (fun _ _ _ _ hle t => unitHomOn_restrict E hle t)
    (fun n => T.unitHomAt E n) (fun n => T.bijective_unitHomAt E n)
    (fun n m hnm x => T.unitHomAt_trans E n m hnm x)
    (fun _ hW n t => T.unitHomAt_sectionsAt E hW n t) h

/-- The converse of `IsSectionsComplete.of_isHomsComplete_unit`, which the same data gives for
free: condition (3) for `ℰ` is condition (4) for the pair `(𝒪_Z, ℰ)`. -/
public theorem IsSectionsComplete.isHomsComplete_unit (h : T.IsSectionsComplete E) :
    T.IsHomsComplete (SheafOfModules.unit Z.ringCatSheaf) E :=
  T.isHomsComplete_of_isSectionsComplete E (SheafOfModules.unit Z.ringCatSheaf) E
    (fun W _ => unitHomOn E W) (fun W _ => bijective_unitHomOn E W)
    (fun _ _ _ _ hle t => unitHomOn_restrict E hle t)
    (fun n => T.unitHomAt E n) (fun n => T.bijective_unitHomAt E n)
    (fun n m hnm x => T.unitHomAt_trans E n m hnm x)
    (fun _ hW n t => T.unitHomAt_sectionsAt E hW n t) h

end InfinitesimalTower

end Stacks.Algebraization

end
