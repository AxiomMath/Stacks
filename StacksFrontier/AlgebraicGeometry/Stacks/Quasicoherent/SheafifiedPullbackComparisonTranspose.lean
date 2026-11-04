module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonConjugate

/-!
# The adjunct of a morphism out of a sheafified Stacks 06WC pullback, peeled to presheaves

`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction` presents
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` — the Stacks 06WC pullback of presheaves
of modules, sheafified — as a left adjoint of the pushforward along the morphism of ringed sites
`ε_a` of **Stacks 070R (2)**.  Every statement about a morphism out of a value of that functor is
proved by transposing it, and the transpose is produced by
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison_map_comp_of_homEquiv`.  To *use* that
transpose one has to know what the adjunct of a concrete morphism is, and no construction says
so: the adjunction is `CategoryTheory.Adjunction.ofNatIsoLeft` of Mathlib's
`SheafOfModules.PullbackConstruction.adjunction`, which is itself `Adjunction.mkOfHomEquiv` of a
composite of three bijections.

This file peels those layers off.  The answer is the one the composition law of **Stacks 075D (1)**
is stated at: the adjunct of a morphism of sheaves of modules out of the sheafified pullback is
the adjunct, along the pullback–pushforward adjunction of *presheaves* of modules, of the
corresponding morphism of presheaves — the one the sheafification bijection produces — read
through the identification of the map `a_{small}^♯` of **Stacks 06WC** with the structure map of
`ε_a`.

## The three layers

* `CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_apply` strips the transport along
  `AlgebraicGeometry.Stack.pullbackConstructionComparisonIso`, leaving a composition with
  the sheafification of
  `AlgebraicGeometry.Stack.smallEtalePullbackComparisonIso`, which
  `CategoryTheory.Adjunction.homEquiv_naturality_left` moves inside the bijection;
* `Stacks.SheafOfModules.pullbackConstructionAdjunction_homEquiv_val` splits Mathlib's
  construction into the sheafification bijection followed by the pullback bijection of presheaves
  of modules — this holds by `rfl`, the construction being `Adjunction.mkOfHomEquiv` of exactly
  that composite;
* `Stacks.PresheafOfModules.homEquiv_pullbackCongr_inv_app_comp` passes from the pullback along
  the structure map of `ε_a` to the pullback along `a_{small}^♯`, the two being compared by
  `PresheafOfModules.pullbackCongr` at an equality of maps of presheaves of rings.

## Main results

* `Stacks.PresheafOfModules.homEquiv_pullbackCongr_inv_app_comp`: transposing a morphism
  precomposed with `PresheafOfModules.pullbackCongr` along the adjunction at the second map is
  transposing it along the adjunction at the first and reindexing the pushforward.
* `Stacks.SheafOfModules.pullbackConstructionAdjunction_homEquiv_val`: the hom-set bijection of
  Mathlib's construction of the pullback of sheaves of modules, on underlying presheaves.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction_homEquiv_val` and
  `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val`: **the
  adjunct of a morphism out of a sheafified Stacks 06WC pullback**, in general and for a morphism
  presented as the one the sheafification bijection produces from a morphism of presheaves.
* `AlgebraicGeometry.Stack.sheafPushforwardCompCell_val_app_apply` and
  `AlgebraicGeometry.Stack.presheafPushforwardCompCell_app_apply`: the two composition cells for
  the pushforwards — the one of sheaves of modules along `ε` which the conjugate of
  `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` is, and the one of presheaves of
  modules along `a_{small}^♯` which
  `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_comp` is stated at — are *the same
  restriction map* of the module being pushed forward, along the identification of the two
  successive base changes with the base change along the composite.
* `Stacks.PresheafOfModules.pushforwardCell_bridge`: consequently, at equal maps of presheaves of
  rings, the two cells agree up to the reindexing isomorphisms.
* `Stacks.CategoryTheory.paste_transposed_square`: the pasting of those pieces, in an abstract
  category.

## Implementation notes

Every statement here is about `PresheafOfModules.pushforward` taken along the structure map of
`ε_a`, whose presheaves of rings are indexed by `E.obj (p.obj x).left.1 (contains_base …)` while
the maps `a_{small}^♯` of Stacks 06WC are indexed by `(p.obj x).left.1`.  The two are only
*definitionally* equal, so the elaborator must reconcile them, and a tactic left to do that on a
large composite runs past its heartbeat ceiling.  The two statements that compare the spellings —
`AlgebraicGeometry.Stack.sheafPushforwardCompCell_val_app_apply` and
`Stacks.PresheafOfModules.pushforwardCell_bridge` — are therefore stated with the sections of the
pushforward spelled on the side of `a_{small}^♯`, and the category algebra that consumes them is
`Stacks.CategoryTheory.paste_transposed_square`, an abstract-category statement with every object
a variable.

No Stacks tag is registered.  Stacks 075D (1) is tagged where it is proved; what is here is the
transposition machinery its sheafified form is consumed by.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u v

namespace Stacks.CategoryTheory

/-- **The pasting that turns a transposed composition law into the law itself.**  The left-hand
side `pv` of the law splits as `a ≫ e`, its second factor `qv` as `m1 ≫ m2`, and its right-hand
side `rv` as `ac ≫ ec`; `hn` moves the reindexing `e` across `m1`, `hb` identifies the resulting
tail with the one the law on the other side carries, and `hh` is that law.

Stating this with every object a variable is not stylistic: the objects it is used at are
pushforwards along two only definitionally equal spellings of one map of presheaves of rings, and
a composite of them is not type-correct at the transparency a rewriting tactic works at. -/
public theorem paste_transposed_square {A : Type u₁} [Category.{v₁} A]
    {M Xc Xe Yc Ym Ye Z Zc : A}
    (pv : M ⟶ Xe) (qv : Xe ⟶ Ye) (tS : Ye ⟶ Z) (rv : M ⟶ Z)
    (a : M ⟶ Xc) (e : Xc ⟶ Xe) (m1 : Xe ⟶ Ym) (m2 : Ym ⟶ Ye)
    (n1 : Xc ⟶ Yc) (n2 : Yc ⟶ Ym) (tP : Yc ⟶ Zc) (ec : Zc ⟶ Z) (ac : M ⟶ Zc)
    (hp : pv = a ≫ e) (hq : qv = m1 ≫ m2) (hr : rv = ac ≫ ec)
    (hn : e ≫ m1 = n1 ≫ n2) (hb : n2 ≫ m2 ≫ tS = tP ≫ ec)
    (hh : (a ≫ n1) ≫ tP = ac) :
    (pv ≫ qv) ≫ tS = rv := by
  rw [hp, hq, hr, ← hh]
  simp only [Category.assoc]
  rw [reassoc_of% hn, hb]

end Stacks.CategoryTheory

namespace Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The adjunct of a morphism out of a pullback of presheaves of modules, read at an equal map
of presheaves of rings.**  For `hab : a = b`, `PresheafOfModules.pullbackCongr hab` compares the
two pullback functors; transposing a morphism out of the pullback along `a`, precomposed with
that comparison, along the adjunction at `b` is transposing it along the adjunction at `a` and
reindexing the pushforward along the same equality.

This is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp`, the comparison being
by definition the canonical one of two left adjoints of the pushforward along `a`, together with
`CategoryTheory.Adjunction.homEquiv_ofNatIsoRight_apply` for the transport that makes the
pushforward along `b` a right adjoint of the pullback along `b`. -/
public theorem homEquiv_pullbackCongr_inv_app_comp {a b : S ⟶ F.op ⋙ R} (hab : a = b)
    [(_root_.PresheafOfModules.pushforward.{u} a).IsRightAdjoint]
    [(_root_.PresheafOfModules.pushforward.{u} b).IsRightAdjoint]
    (X : _root_.PresheafOfModules.{u} S) (Y : _root_.PresheafOfModules.{u} R)
    (f : (_root_.PresheafOfModules.pullback.{u} a).obj X ⟶ Y) :
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).homEquiv X Y
        ((_root_.PresheafOfModules.pullbackCongr hab).inv.app X ≫ f) =
      (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a).homEquiv X Y f ≫
        (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
          hab)).hom.app Y := by
  have key := Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a)
    ((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).ofNatIsoRight
      (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k) hab.symm)))
    ((_root_.PresheafOfModules.pullbackCongr hab).inv.app X ≫ f)
  rw [show (Adjunction.leftAdjointUniq
      (_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} a)
      ((_root_.PresheafOfModules.pullbackPushforwardAdjunction.{u} b).ofNatIsoRight
        (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k) hab.symm)))) =
      _root_.PresheafOfModules.pullbackCongr hab from rfl, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp,
    Adjunction.homEquiv_ofNatIsoRight_apply] at key
  rw [key, Category.assoc, ← NatTrans.comp_app, eqToIso.hom, eqToIso.hom, eqToHom_trans,
    eqToHom_refl, NatTrans.id_app, Category.comp_id]

/-- A pushforward of a morphism of presheaves of modules acts on sections as the morphism itself,
at the image object. -/
public theorem pushforward_map_app_apply (a : S ⟶ F.op ⋙ R)
    {M N : _root_.PresheafOfModules.{u} R} (g : M ⟶ N) (W : Cᵒᵖ)
    (m : ((_root_.PresheafOfModules.pushforward.{u} a).obj M).obj W) :
    ((_root_.PresheafOfModules.pushforward.{u} a).map g).app W m = g.app (F.op.obj W) m := rfl

/-- The reindexing of a pushforward of presheaves of modules along an *equality* of maps of
presheaves of rings is the identity on sections: only the module structure is transported. -/
public theorem eqToIso_pushforward_hom_app_app_apply {a b : S ⟶ F.op ⋙ R} (hab : a = b)
    (M : _root_.PresheafOfModules.{u} R) (W : Cᵒᵖ)
    (m : ((_root_.PresheafOfModules.pushforward.{u} a).obj M).obj W) :
    ((eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
      hab)).hom.app M).app W m = m := by
  subst hab
  rfl

/-- **Two composition cells for the pushforwards of presheaves of modules which agree on
sections agree, up to the reindexings along equalities of the maps of presheaves of rings.**

The cell `tS` lives at the maps `bψ`, `bφ`, `bc` and the cell `tP` at the equal maps `aψ`, `aφ`,
`ac`; the three reindexings `Stacks.PresheafOfModules.eqToIso_pushforward_hom_app_app_apply` are
the identity on sections, so the hypothesis that `tS` and `tP` act the same way on sections is
all that is needed.  Substituting the three equalities reduces the statement to exactly that
hypothesis. -/
public theorem pushforwardCell_bridge {Cx : Type u₁} [Category.{v₁} Cx] {Cy : Type u₂}
    [Category.{v₂} Cy] {Cz : Type u₃} [Category.{v₃} Cz]
    {Kφ : Cy ⥤ Cx} {Kψ : Cz ⥤ Cy} {Kc : Cz ⥤ Cx}
    {Rx : Cxᵒᵖ ⥤ RingCat.{u}} {Ry : Cyᵒᵖ ⥤ RingCat.{u}} {Rz : Czᵒᵖ ⥤ RingCat.{u}}
    {aφ bφ : Ry ⟶ Kφ.op ⋙ Rx} (hφ : aφ = bφ)
    {aψ bψ : Rz ⟶ Kψ.op ⋙ Ry} (hψ : aψ = bψ)
    {ac bc : Rz ⟶ Kc.op ⋙ Rx} (hc : ac = bc)
    (M : _root_.PresheafOfModules.{u} Rx)
    (tS : (_root_.PresheafOfModules.pushforward.{u} bψ).obj
        ((_root_.PresheafOfModules.pushforward.{u} bφ).obj M) ⟶
      (_root_.PresheafOfModules.pushforward.{u} bc).obj M)
    (tP : (_root_.PresheafOfModules.pushforward.{u} aψ).obj
        ((_root_.PresheafOfModules.pushforward.{u} aφ).obj M) ⟶
      (_root_.PresheafOfModules.pushforward.{u} ac).obj M)
    (hcomm : ∀ (W : Czᵒᵖ)
      (m : ((_root_.PresheafOfModules.pushforward.{u} bψ).obj
        ((_root_.PresheafOfModules.pushforward.{u} bφ).obj M)).obj W),
      tS.app W m = tP.app W m) :
    (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k) hψ)).hom.app
          ((_root_.PresheafOfModules.pushforward.{u} aφ).obj M) ≫
        (_root_.PresheafOfModules.pushforward.{u} bψ).map
            ((eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
              hφ)).hom.app M) ≫
          tS =
      tP ≫ (eqToIso (congrArg (fun k => _root_.PresheafOfModules.pushforward.{u} k)
        hc)).hom.app M := by
  subst hφ hψ hc
  refine _root_.PresheafOfModules.hom_ext fun W => ?_
  refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun m => ?_)
  simpa using hcomm W m

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]

/-- **The hom-set bijection of Mathlib's construction of the pullback of sheaves of modules, on
underlying presheaves.**  `SheafOfModules.PullbackConstruction.adjunction` is
`CategoryTheory.Adjunction.mkOfHomEquiv` of the sheafification bijection followed by the
pullback–pushforward bijection of presheaves of modules and the full faithfulness of the
forgetful functor, so this holds by `rfl`.

It is the middle of the three layers that separate a morphism out of a sheafified pullback from
the morphism of presheaves of modules it is the adjunct of. -/
public theorem pullbackConstructionAdjunction_homEquiv_val
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint]
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : _root_.SheafOfModules.{u} S) (G : _root_.SheafOfModules.{u} R)
    (t : (_root_.SheafOfModules.forget S ⋙ PresheafOfModules.pullback.{u} φ.hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)).obj M ⟶ G) :
    ((_root_.SheafOfModules.PullbackConstruction.adjunction.{u} φ).homEquiv M G t).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} φ.hom).homEquiv M.val G.val
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ G t) := rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- **The adjunct of a morphism out of a sheafified Stacks 06WC pullback.**  For an arrow
`φ : x ⟶ y` of `𝒳` and a morphism `t` of sheaves of modules out of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` of `M`, the adjunct of `t` along
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction` has, as its underlying morphism
of presheaves of modules, the adjunct along the pullback–pushforward adjunction of presheaves of
modules at the map `a_{small}^♯` of **Stacks 06WC** of the sheafification-adjunct of `t`,
followed by the reindexing of the pushforward along
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`.

This is what makes the transposed form of a composition law usable: on the right-hand side every
adjunct is one of *presheaves* of modules, which is restriction of sections, and that is where
**Stacks 075D (1)** is proved.  Three layers are peeled off — the transport along
`AlgebraicGeometry.Stack.pullbackConstructionComparisonIso`, the sheafification bijection, and
the comparison of the two pullbacks of presheaves of modules. -/
public theorem sheafifiedPullbackComparisonAdjunction_homEquiv_val
    (M : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)))
    (G : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (t : (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).obj M ⟶ G) :
    ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ).homEquiv M G t).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ G t) ≫
      (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
        (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing
          B E h S hS p hp τ hτ φ))).hom.app G.val := by
  refine Eq.trans (congrArg (fun k => SheafOfModules.Hom.val k)
    (Adjunction.homEquiv_ofNatIsoLeft_apply
      (SheafOfModules.PullbackConstruction.adjunction.{u}
        (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
      (pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ) t)) ?_
  refine Eq.trans (Stacks.SheafOfModules.pullbackConstructionAdjunction_homEquiv_val
    (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)) M G _) ?_
  refine Eq.trans (congrArg
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)).hom).homEquiv M.val G.val)
    (Adjunction.homEquiv_naturality_left
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj))
      ((smallEtalePullbackComparisonIso B E h S hS p hp τ hτ φ).inv.app M.val) t)) ?_
  exact Stacks.PresheafOfModules.homEquiv_pullbackCongr_inv_app_comp _ _ _ _

/-- `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction_homEquiv_val` for a morphism
presented as the one the sheafification bijection produces from a morphism of presheaves of
modules out of the Stacks 06WC pullback.  This is the shape every leg of the identification of
sections of **Stacks 076T** arrives in, the sheafification unit being invertible there. -/
public theorem sheafifiedPullbackComparisonAdjunction_homEquiv_symm_val
    (M : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
      (contains_base B E h S hS p y)))
    (G : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (w : (PresheafOfModules.pullback.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M.val ⟶ G.val) :
    ((sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ).homEquiv M G
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _ G).symm w)).val =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val w ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing
            B E h S hS p hp τ hτ φ))).hom.app G.val :=
  Eq.trans
    (sheafifiedPullbackComparisonAdjunction_homEquiv_val B E h S hS p hp τ hτ φ M G _)
    (congrArg (fun t => (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv M.val G.val t ≫
        (eqToIso (congrArg (fun k => PresheafOfModules.pushforward.{u} k)
          (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing
            B E h S hS p hp τ hτ φ))).hom.app G.val)
      (Equiv.apply_symm_apply _ w))

/-- **The composition cell for the pushforwards of sheaves of modules along `ε` is restriction of
sections along the identification of the two successive base changes.**  This is the 2-cell that
`AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonCompIso_inv` identifies the
conjugate of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` with: Mathlib's
comparison of the two composite pushforwards, which is the identity on sections, followed by the
reindexing `AlgebraicGeometry.SmallEtale.smallEtalePushforwardFactoredCompIso`, which is the
restriction map along `AlgebraicGeometry.Stack.smallEtaleBaseChangeCompIso`.

The sections are spelled on the side of the maps `a_{small}^♯` of Stacks 06WC rather than on the
side of the structure maps of `ε`: the two are only definitionally equal, and this is the
spelling `Stacks.PresheafOfModules.pushforwardCell_bridge` consumes. -/
public theorem sheafPushforwardCompCell_val_app_apply
    (𝓜 : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)))
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (m : ((PresheafOfModules.pushforward.{u}
        (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p ψ)).hom).obj
      ((PresheafOfModules.pushforward.{u}
        (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ)).hom).obj 𝓜.val)).obj W) :
    (((SheafOfModules.pushforwardComp.{u}
            (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p ψ))
            (SmallEtale.smallEtaleStructureMapRing E
              (smallEtaleBaseMorphism B E h S hS p φ))).hom ≫
          (SmallEtale.smallEtalePushforwardFactoredCompIso E
            (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
            (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
            (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).inv).app 𝓜).val.app W m =
      𝓜.val.map ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).inv.app W.unop).op m := by
  simp only [SheafOfModules.pushforwardCongr₂, SmallEtale.smallEtalePushforwardFactoredCompIso,
    Iso.trans_inv, SheafOfModules.pushforwardNatIso_inv, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app]
  rfl

/-- **The composition cell for the pushforwards of presheaves of modules along the maps
`a_{small}^♯` of Stacks 06WC is the same restriction of sections.**  This is the 2-cell that
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_comp` — the composition law of
**Stacks 075D (1)** for the direct-image comparison of Stacks 06WC — is stated at.

Together with `AlgebraicGeometry.Stack.sheafPushforwardCompCell_val_app_apply` this says that the
sheaf-level and presheaf-level composition cells act identically on sections, which is the
hypothesis of `Stacks.PresheafOfModules.pushforwardCell_bridge`. -/
public theorem presheafPushforwardCompCell_app_apply
    (M : PresheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj)
    (W : (SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))ᵒᵖ)
    (m : ((PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).obj
      ((PresheafOfModules.pushforward.{u}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj M)).obj W) :
    (((PresheafOfModules.pushforwardComp.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).hom ≫
          (smallEtalePushforwardComparisonCompIso B E h S hS p hp τ hτ φ ψ).inv).app M).app W m =
      M.map ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).inv.app W.unop).op m := by
  simp only [smallEtalePushforwardComparisonCompIso, NatTrans.comp_app,
    PresheafOfModules.comp_app, CategoryTheory.comp_apply,
    Stacks.PresheafOfModules.pushforwardIsoOfIndexIso_inv_app_app_apply]
  rfl

end AlgebraicGeometry.Stack

end
