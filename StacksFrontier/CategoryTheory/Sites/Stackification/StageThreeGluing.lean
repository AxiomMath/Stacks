module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeMorSheaf

/-!
# The morphism presheaves of the third stage are sheaves

`StacksFrontier/CategoryTheory/Sites/Stackification/StageThreeMorSheaf.lean`
proves the separatedness
half of condition (2) of Stacks 026F for the third stage of the construction of the stackification
and reduces the condition to the gluing half alone. This file proves that gluing half,
`CategoryTheory.Functor.exists_amalgamation_descentPairProj`, and draws the conclusion.

A morphism of the third stage out of `A` over `u : A.pt ⟶ B.pt` is, up to the identification of
data agreeing on a covering sieve, a family of morphisms `A.datum.obj f ⟶ B.datum.obj (f ≫ u)` of
the fibres, indexed by the arrows `f` of a covering sieve and compatible with the gluing
isomorphisms of the two descent data. So a compatible family of morphisms `F Φ : W ⟶ B` indexed by
the morphisms `Φ : W ⟶ A` lying over a covering sieve `S` has to be turned into one such family.

The family is read off from the canonical morphisms out of the pullbacks of `A`: for an arrow `h`
of `S` the value of the given family at `CategoryTheory.Functor.DescentPairData.pullbackHom A h` is
a morphism `A.pullback h ⟶ B` lying over `h ≫ u`, and a representative of it is a family of
morphisms of fibres defined on a covering sieve of the source of `h` — not a single morphism
`A.datum.obj h ⟶ B.datum.obj (h ≫ u)`. Producing that single morphism is a gluing problem *in the
fibre*, and it is solved by the sheaf condition for the morphism presheaves of `p` itself, which
the first two stages of the construction supply: this is
`CategoryTheory.Functor.exists_fiberHom_of_descentPairHom`, an application of
`CategoryTheory.Functor.exists_fiberHom_of_locally`. Separatedness alone would not do; only the
uniqueness of the glued morphism comes from separatedness.

The two remaining obligations on the resulting family are that it is compatible with the gluing
isomorphisms and that it restricts to the given family. Both follow from a single statement,
`hstar` inside `CategoryTheory.Functor.exists_amalgamation_descentPairProj`: the glued morphism at
`h`, base changed along `ε`, is the glued morphism at `ε ≫ h`, read between the chosen pullbacks
by the contractions `CategoryTheory.Functor.SieveDescentDatum.contract` of the two data. Granting
it, compatibility with the gluing isomorphisms is the identity
`CategoryTheory.Functor.SieveDescentDatum.contract_hom_comp_contract_inv`, that two contractions
onto one and the same object compose to a gluing isomorphism.

## Main results

* `CategoryTheory.Functor.SieveDescentDatum.contract_hom_comp_contract_inv`, the gluing
  isomorphisms expressed by the contractions;
* `CategoryTheory.Functor.DescentPairHom.contract_comp_map`, the compatibility of the family of
  morphisms a morphism datum consists of with restriction;
* `CategoryTheory.Functor.exists_fiberHom_of_descentPairHom`, the gluing of that family into one
  morphism of the fibre;
* `CategoryTheory.Functor.exists_amalgamation_descentPairProj`, the gluing half of condition (2)
  of Stacks 026F for the third stage;
* `CategoryTheory.Functor.isMorSheaf_descentPairProj` and
  `CategoryTheory.Functor.isMorSheaf_stageThreeProj`, condition (2) of Stacks 026F itself, for the
  third stage and for the composite of the three stages.

## Obligations that remain before Stacks 02ZN

This file carries no `@[stacks 02ZN]` tag and nothing here may be read as claiming Stacks 02ZN.
Condition (2) of Stacks 026F is one clause of several. What remains is clause (1) of Stacks 02ZN
for `CategoryTheory.Functor.toStageThree` — local injectivity and local surjectivity of
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` — condition (2) of Stacks 026F for the
composite of the first two stages in the form
`CategoryTheory.Functor.HasEffectiveDescent` asks for,
`CategoryTheory.Functor.HasEffectiveDescent` for `CategoryTheory.Functor.descentPairProj` itself,
and the assembly of Stacks 02ZN from those.
-/

@[expose] public section

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

open CategoryTheory Category

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {J : GrothendieckTopology 𝒮}

/-- The contraction of a descent datum onto one of its objects, taken at two arrows with the same
target object, composes to the gluing isomorphism of the two arrows. -/
theorem SieveDescentDatum.contract_hom_comp_contract_inv {U : 𝒮} {R : Sieve U}
    (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) {b : Z ⟶ U} (hb : R b) (h : ε ≫ f = b) (h' : ε' ≫ g = b)
    (heq : ε ≫ f = ε' ≫ g) :
    (D.contract hf ε hb h).hom ≫ (D.contract hg ε' hb h').inv =
      (D.iso hf hg ε ε' heq).hom := by
  rw [contract, contract, Iso.trans_hom, Iso.trans_inv, assoc, Iso.hom_inv_id_assoc,
    ← D.iso_symm hg hb ε' (𝟙 Z) (by rw [id_comp, h']),
    D.cocycle hf hb hg ε (𝟙 Z) ε' (by rw [h, id_comp]) (by rw [id_comp, h']) heq]

/-- **The base change of the inverse of a contraction.** The inverse form of
`CategoryTheory.Functor.SieveDescentDatum.pullbackFiberHom_contract`. -/
theorem SieveDescentDatum.pullbackFiberHom_contract_inv_comp {U : 𝒮} {R : Sieve U}
    (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) (g : W ⟶ V) {a : W ⟶ U}
    (ha : R a) (hga : g ≫ f = a) (ε : Z ⟶ W) :
    pullbackFiberHom (D.contract hf g ha hga).inv ε ≫
        (pullbackFiberCompIso (D.obj f hf) g ε).hom =
      (D.iso hf ha (ε ≫ g) ε (by rw [assoc, hga])).inv := by
  have hiso : pullbackFiberIso (D.contract hf g ha hga) ε =
      pullbackFiberCompIso (D.obj f hf) g ε ≪≫
        D.iso hf ha (ε ≫ g) ε (by rw [assoc, hga]) :=
    Iso.ext (by simpa using D.pullbackFiberHom_contract hf g ha hga ε)
  have h2 : pullbackFiberHom (D.contract hf g ha hga).inv ε =
      (pullbackFiberIso (D.contract hf g ha hga) ε).inv := rfl
  rw [h2, hiso]
  simp

/-- `CategoryTheory.Functor.SieveDescentDatum.pullbackFiberHom_contract_inv_comp` solved for the
base change. -/
theorem SieveDescentDatum.pullbackFiberHom_contract_inv {U : 𝒮} {R : Sieve U}
    (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) (g : W ⟶ V) {a : W ⟶ U}
    (ha : R a) (hga : g ≫ f = a) (ε : Z ⟶ W) :
    pullbackFiberHom (D.contract hf g ha hga).inv ε =
      (D.iso hf ha (ε ≫ g) ε (by rw [assoc, hga])).inv ≫
        (pullbackFiberCompIso (D.obj f hf) g ε).inv := by
  rw [← D.pullbackFiberHom_contract_inv_comp hf g ha hga ε, assoc, Iso.hom_inv_id, comp_id]

/-- The contraction of a descent datum onto one of its objects does not depend on which of two
equal arrows the object is read at. -/
theorem SieveDescentDatum.contract_hom_congr_tgt {U : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R)
    {V Z : 𝒮} {a : V ⟶ U} (ha : R a) (ε : Z ⟶ V) {b b' : Z ⟶ U} (hb : R b) (hb' : R b')
    (h : ε ≫ a = b) (h' : ε ≫ a = b') (e : D.obj b hb = D.obj b' hb') :
    (D.contract ha ε hb h).hom ≫ eqToHom e = (D.contract ha ε hb' h').hom := by
  obtain rfl : b = b' := h.symm.trans h'
  obtain rfl : hb = hb' := rfl
  obtain rfl : h = h' := rfl
  simp

/-- The contraction of a pulled back descent datum is the contraction of the datum itself. -/
theorem SieveDescentDatum.pullback_contract {U U' : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R)
    (v : U' ⟶ U) {V Z : 𝒮} {a : V ⟶ U'} (ha : (R.pullback v).arrows a) (ε : Z ⟶ V)
    {b : Z ⟶ U'} (hb : (R.pullback v).arrows b) (h : ε ≫ a = b) :
    (D.pullback v).contract ha ε hb h =
      D.contract ha ε hb (show ε ≫ (a ≫ v) = b ≫ v by rw [← assoc, h]) := rfl

/-- **The morphisms a morphism datum of descent pairs attaches to an arrow and to a further
restriction of it are intertwined by the contractions of the two data.** This is the compatibility
of the family `f ↦ Y.map f` with restriction, in the form the sheaf condition for the morphism
presheaves of `p` asks for. -/
theorem DescentPairHom.contract_comp_map {A B : DescentPair p J} {w : A.pt ⟶ B.pt}
    (Y : DescentPairHom A B w) {V W₀ : 𝒮} (δ : V ⟶ A.pt) (hδ : Y.sieve.arrows δ)
    (γ : W₀ ⟶ V) (hγδ : Y.sieve.arrows (γ ≫ δ))
    {g : V ⟶ B.pt} (hg : B.sieve.arrows g) (pf : δ ≫ w = g)
    {g₂ : W₀ ⟶ B.pt} (hg₂ : B.sieve.arrows g₂) (pf₂ : (γ ≫ δ) ≫ w = g₂)
    (hga : γ ≫ g = g₂) :
    (A.datum.contract (Y.le_dom _ hδ) γ (Y.le_dom _ hγδ) rfl).hom ≫ Y.map (γ ≫ δ) hγδ hg₂ pf₂ =
      pullbackFiberHom (Y.map δ hδ hg pf) γ ≫ (B.datum.contract hg γ hg₂ hga).hom := by
  have ha : (𝟙 W₀) ≫ (γ ≫ δ) = γ ≫ δ := id_comp _
  have hb : (𝟙 W₀) ≫ g₂ = γ ≫ g := by rw [id_comp, hga]
  have hmg := Y.map_glue (γ ≫ δ) hγδ δ hδ hg₂ pf₂ hg pf (𝟙 W₀) γ ha
  rw [A.datum.iso_symm (Y.le_dom _ hδ) (Y.le_dom _ hγδ) γ (𝟙 W₀) ha.symm,
    B.datum.iso_symm hg hg₂ γ (𝟙 W₀) hb.symm, Iso.comp_inv_eq] at hmg
  have key : pullbackFiberHom (Y.map δ hδ hg pf) γ ≫
        (B.datum.iso hg hg₂ γ (𝟙 W₀) hb.symm).hom =
      (A.datum.iso (Y.le_dom _ hδ) (Y.le_dom _ hγδ) γ (𝟙 W₀) ha.symm).hom ≫
        pullbackFiberHom (Y.map (γ ≫ δ) hγδ hg₂ pf₂) (𝟙 W₀) := by
    rw [hmg]
    simp
  simp only [SieveDescentDatum.contract, Iso.trans_hom, assoc]
  rw [← pullbackFiberHom_id_base (Y.map (γ ≫ δ) hγδ hg₂ pf₂), ← assoc, ← key, assoc]

/-- The canonical morphism datum from the pullback of a descent pair along a composite `e ≫ f` to
its pullback along `f`, lying over `e`. -/
@[implicit_reducible]
def DescentPairData.pullbackComp (A : DescentPair p J) {V V' : 𝒮} (f : V ⟶ A.pt) (e : V' ⟶ V)
    (k : V' ⟶ A.pt) (hbase : k = e ≫ f) : DescentPairData (A.pullback k) (A.pullback f) :=
  ⟨e, DescentPairHom.pullbackLift (DescentPairData.pullbackHom A k) f e hbase⟩

/-- The canonical morphism datum `DescentPairData.pullbackComp A f e k hbase` lies over `e`. -/
@[simp]
theorem DescentPairData.pullbackComp_base (A : DescentPair p J) {V V' : 𝒮} (f : V ⟶ A.pt)
    (e : V' ⟶ V) (k : V' ⟶ A.pt) (hbase : k = e ≫ f) :
    (DescentPairData.pullbackComp A f e k hbase).base = e := rfl

/-- The canonical morphism of pullbacks attaches a transport to each arrow of its sieve. -/
theorem DescentPairData.pullbackComp_hom_map (A : DescentPair p J) {V V' : 𝒮} (f : V ⟶ A.pt)
    (e : V' ⟶ V) (k : V' ⟶ A.pt) (hbase : k = e ≫ f) {V₀ : 𝒮} (δ : V₀ ⟶ V')
    (hδ : (DescentPairData.pullbackComp A f e k hbase).hom.sieve.arrows δ) {g : V₀ ⟶ V}
    (hg : (A.pullback f).sieve.arrows g) (pf : δ ≫ e = g)
    (eq : (A.pullback k).datum.obj δ
        ((DescentPairData.pullbackComp A f e k hbase).hom.le_dom _ hδ) =
      (A.pullback f).datum.obj g hg) :
    (DescentPairData.pullbackComp A f e k hbase).hom.map δ hδ hg pf = eqToHom eq := rfl

/-- The canonical morphism of pullbacks, followed by the canonical morphism from the pullback along
`f`, is the canonical morphism from the pullback along `e ≫ f`. -/
theorem pullbackComp_comp_pullbackHom (A : DescentPair p J) {V V' : 𝒮} (f : V ⟶ A.pt)
    (e : V' ⟶ V) (k : V' ⟶ A.pt) (hbase : k = e ≫ f) :
    ((DescentMor.mk (DescentPairData.pullbackComp A f e k hbase) :
          A.pullback k ⟶ A.pullback f) ≫
        DescentMor.mk (DescentPairData.pullbackHom A f) : A.pullback k ⟶ A) =
      DescentMor.mk (DescentPairData.pullbackHom A k) := by
  refine (DescentMor.mk_eq_iff _ _).mpr (DescentPairData.rel_of_agree hbase.symm ?_)
  intro V₀ δ hδ hδ' g hg hh hh'
  exact DescentPairHom.map_target_congr (DescentPairData.pullbackHom A k).hom δ hδ'
    ((assoc δ e f).trans hh) hδ.2 hg ((congrArg (δ ≫ ·) hbase).trans (assoc δ e f).symm) hh'

/-- The inverse form of
`CategoryTheory.Functor.SieveDescentDatum.contract_hom_comp_contract_inv`. -/
theorem SieveDescentDatum.contract_hom_comp_contract_inv' {U : 𝒮} {R : Sieve U}
    (D : SieveDescentDatum p R) {V W Z : 𝒮} {f : V ⟶ U} (hf : R f) {g : W ⟶ U} (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) {b : Z ⟶ U} (hb : R b) (h : ε ≫ f = b) (h' : ε' ≫ g = b)
    (heq : ε ≫ f = ε' ≫ g) :
    (D.contract hg ε' hb h').hom ≫ (D.contract hf ε hb h).inv =
      (D.iso hf hg ε ε' heq).inv := by
  rw [D.contract_hom_comp_contract_inv hg hf ε' ε hb h' h heq.symm, D.iso_symm hf hg ε ε' heq]

/-- An arrow of the defining sieve of a morphism datum out of a pullback of `A`, read as an arrow
of the covering sieve of `A`. Stating the type in this form, rather than leaving it as membership
in the pullback sieve, is what keeps the terms below type-correct at the `implicit` transparency
`rw` checks its motives at. -/
theorem DescentPairHom.le_dom_pullback {A B : DescentPair p J} {V : 𝒮} {f : V ⟶ A.pt}
    {w : V ⟶ B.pt} (Y : DescentPairHom (A.pullback f) B w) {W : 𝒮} {δ : W ⟶ V}
    (hδ : Y.sieve.arrows δ) : A.sieve.arrows (δ ≫ f) := Y.le_dom _ hδ

/-- The family of morphisms of fibres that a morphism datum out of the pullback of `A` along `f`
prescribes over the arrows of its defining sieve: the morphism it attaches to an arrow, read
between the chosen pullbacks by the contractions of the two descent data. -/
noncomputable def descentMorLocal {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {V : 𝒮} {f : V ⟶ A.pt}
    (hfA : A.sieve.arrows f) {g : V ⟶ B.pt} (hg : B.sieve.arrows g) (pf : f ≫ u = g)
    (Y : DescentPairHom (A.pullback f) B (f ≫ u)) ⦃W : 𝒮⦄ (δ : W ⟶ V) (hδ : Y.sieve.arrows δ) :
    pullbackFiber p (A.datum.obj f hfA) δ ⟶ pullbackFiber p (B.datum.obj g hg) δ :=
  (A.datum.contract hfA δ (Y.le_dom_pullback hδ) rfl).hom ≫
    Y.map δ hδ (B.sieve.downward_closed hg δ) (by rw [pf]) ≫
    (B.datum.contract hg δ (B.sieve.downward_closed hg δ) rfl).inv

/-- **A morphism datum out of the pullback of `A` along an arrow `f` of its covering sieve glues to
a morphism of fibres**, as soon as the morphism presheaves of `p` are sheaves: its values at the
arrows of its defining sieve form a compatible family of sections of `Mor(A.datum.obj f,
B.datum.obj g)`. -/
theorem exists_fiberHom_of_descentPairHom
    (hmor : ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y)
    {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {V : 𝒮} {f : V ⟶ A.pt}
    (hfA : A.sieve.arrows f) {g : V ⟶ B.pt} (hg : B.sieve.arrows g) (pf : f ≫ u = g)
    (Y : DescentPairHom (A.pullback f) B (f ≫ u)) :
    ∃ m : A.datum.obj f hfA ⟶ B.datum.obj g hg,
      ∀ ⦃W : 𝒮⦄ (δ : W ⟶ V) (hδ : Y.sieve.arrows δ),
        pullbackFiberHom m δ = descentMorLocal hfA hg pf Y δ hδ := by
  refine exists_fiberHom_of_locally p (hmor V _ _) Y.sieve_mem (descentMorLocal hfA hg pf Y) ?_
  rintro W₁ W₂ δ hδ γ b rfl hb'
  have hM : (A.datum.contract (Y.le_dom_pullback hδ) γ (Y.le_dom_pullback hb')
        (assoc γ δ f).symm).hom ≫
      Y.map (γ ≫ δ) hb' (B.sieve.downward_closed hg (γ ≫ δ))
        (show (γ ≫ δ) ≫ (f ≫ u) = (γ ≫ δ) ≫ g by rw [pf]) =
      pullbackFiberHom (Y.map δ hδ (B.sieve.downward_closed hg δ)
          (show δ ≫ (f ≫ u) = δ ≫ g by rw [pf])) γ ≫
        (B.datum.contract (B.sieve.downward_closed hg δ) γ
          (B.sieve.downward_closed hg (γ ≫ δ)) (assoc γ δ g).symm).hom :=
    Y.contract_comp_map δ hδ γ hb' (B.sieve.downward_closed hg δ) _
      (B.sieve.downward_closed hg (γ ≫ δ)) _ (assoc γ δ g).symm
  simp only [descentMorLocal, pullbackFiberCompIso'_rfl, pullbackFiberHom_comp, assoc]
  rw [A.datum.pullbackFiberHom_contract hfA δ (Y.le_dom_pullback hδ) rfl γ]
  simp only [assoc, Iso.inv_hom_id_assoc]
  rw [B.datum.pullbackFiberHom_contract_inv_comp hg δ (B.sieve.downward_closed hg δ) rfl γ,
    ← A.datum.contract_hom_comp_contract_inv hfA (Y.le_dom_pullback hδ) (γ ≫ δ) γ
      (Y.le_dom_pullback hb') rfl (assoc γ δ f).symm (assoc γ δ f),
    ← B.datum.contract_hom_comp_contract_inv' hg (B.sieve.downward_closed hg δ) (γ ≫ δ) γ
      (B.sieve.downward_closed hg (γ ≫ δ)) rfl (assoc γ δ g).symm (assoc γ δ g)]
  simp only [assoc]
  rw [Iso.cancel_iso_hom_left, Iso.eq_inv_comp]
  exact ((assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ (B.datum.contract hg (γ ≫ δ)
    (B.sieve.downward_closed hg (γ ≫ δ)) rfl).inv) hM)).trans (assoc _ _ _)

/-- Two objects a descent datum attaches to equal arrows agree. -/
theorem SieveDescentDatum.obj_congr {U : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R) {V : 𝒮}
    {a b : V ⟶ U} (hab : a = b) (ha : R a) (hb : R b) : D.obj a ha = D.obj b hb := by
  subst hab
  rfl

/-- A morphism of the third stage lying over `w` is the class of a morphism datum lying over `w`
on the nose. -/
private theorem DescentMor.exists_hom_of_map_eq {A B : DescentPair p J} {w : A.pt ⟶ B.pt}
    (X : A ⟶ B) (hX : (p.descentPairProj J).map X = w) :
    ∃ Z : DescentPairHom A B w, DescentMor.mk (⟨w, Z⟩ : DescentPairData A B) = X := by
  obtain ⟨⟨w', Z⟩, rfl⟩ := DescentMor.exists_rep X
  obtain rfl : w' = w := hX
  exact ⟨Z, rfl⟩

/-- **A morphism datum out of the pullback of `A` along `ε ≫ h` identified with the restriction of
a morphism datum out of the pullback along `h` agrees with it on a covering sieve.** -/
private theorem DescentPairHom.exists_sieve_map_eq_of_mk_eq {A B : DescentPair p J}
    {u : A.pt ⟶ B.pt} {V V' : 𝒮} {h : V ⟶ A.pt} {ε : V' ⟶ V}
    {Y₁ : DescentPairHom (A.pullback h) B (h ≫ u)}
    {Y₂ : DescentPairHom (A.pullback (ε ≫ h)) B ((ε ≫ h) ≫ u)}
    (hY : DescentMor.mk (⟨(ε ≫ h) ≫ u, Y₂⟩ : DescentPairData (A.pullback (ε ≫ h)) B) =
      DescentMor.mk ((DescentPairData.pullbackComp A h ε (ε ≫ h) rfl).comp ⟨h ≫ u, Y₁⟩)) :
    ∃ Tr : Sieve V', Tr ∈ J V' ∧
      (∀ ⦃V₀ : 𝒮⦄ {γ : V₀ ⟶ V'}, Tr.arrows γ → Y₂.sieve.arrows γ) ∧
      (∀ ⦃V₀ : 𝒮⦄ {γ : V₀ ⟶ V'}, Tr.arrows γ → Y₁.sieve.arrows (γ ≫ ε)) ∧
      ∀ ⦃V₀ : 𝒮⦄ (γ : V₀ ⟶ V') (_ : Tr.arrows γ) {g₀ : V₀ ⟶ B.pt} (hg₀ : B.sieve.arrows g₀)
        (pfa : γ ≫ ((ε ≫ h) ≫ u) = g₀) (pfb : (γ ≫ ε) ≫ (h ≫ u) = g₀)
        (hγk : Y₂.sieve.arrows γ) (hγε : Y₁.sieve.arrows (γ ≫ ε)),
        Y₂.map γ hγk hg₀ pfa =
          eqToHom (A.datum.obj_congr (assoc γ ε h).symm (Y₂.le_dom_pullback hγk)
            (Y₁.le_dom_pullback hγε)) ≫ Y₁.map (γ ≫ ε) hγε hg₀ pfb := by
  obtain ⟨-, Tr, hTr, hle₁, hle₂, hagree⟩ := (DescentMor.mk_eq_iff _ _).mp hY
  refine ⟨Tr, hTr, fun _ _ hγ ↦ hle₁ _ hγ, fun _ _ hγ ↦ (hle₂ _ hγ).2, ?_⟩
  intro V₀ γ hγ g₀ hg₀ pfa pfb hγk hγε
  have h1 := hagree γ hγ hg₀ pfa (show γ ≫ (ε ≫ (h ≫ u)) = g₀ by rwa [← assoc])
  rwa [DescentPairData.comp_hom_map (DescentPairData.pullbackComp A h ε (ε ≫ h) rfl)
    ⟨h ≫ u, Y₁⟩ γ (hle₂ _ hγ).1 (hle₂ _ hγ).2 hg₀ pfb _ _] at h1

/-- A family of morphisms indexed by the morphisms into `A` over a sieve takes equal values at equal
morphisms. -/
private theorem family_congr {A B : DescentPair p J} {S : Sieve A.pt}
    (F : ∀ {W : DescentPair p J} (Φ : W ⟶ A), S.arrows ((p.descentPairProj J).map Φ) → (W ⟶ B))
    {W : DescentPair p J} {Φ₁ Φ₂ : W ⟶ A} (e : Φ₁ = Φ₂)
    (h₁ : S.arrows ((p.descentPairProj J).map Φ₁))
    (h₂ : S.arrows ((p.descentPairProj J).map Φ₂)) : F Φ₁ h₁ = F Φ₂ h₂ := by
  subst e
  rfl

/-- **Representatives of the values of a compatible family at the canonical morphisms out of the
pullbacks along `h` and `ε ≫ h` are related through
`CategoryTheory.Functor.DescentPairData.pullbackComp`.** -/
private theorem mk_eq_pullbackComp_comp_of_compatible {A B : DescentPair p J} {u : A.pt ⟶ B.pt}
    {S : Sieve A.pt}
    (F : ∀ {W : DescentPair p J} (Φ : W ⟶ A), S.arrows ((p.descentPairProj J).map Φ) → (W ⟶ B))
    (hFcomp : ∀ {W W' : DescentPair p J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
      (hΦ : S.arrows ((p.descentPairProj J).map Φ))
      (hΨΦ : S.arrows ((p.descentPairProj J).map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ)
    {V V' : 𝒮} {h : V ⟶ A.pt} (hh : S.arrows h) (ε : V' ⟶ V) (hk : S.arrows (ε ≫ h))
    {Y₁ : DescentPairHom (A.pullback h) B (h ≫ u)}
    {Y₂ : DescentPairHom (A.pullback (ε ≫ h)) B ((ε ≫ h) ≫ u)}
    (hY₁ : DescentMor.mk (⟨h ≫ u, Y₁⟩ : DescentPairData (A.pullback h) B) =
      F (DescentMor.mk (DescentPairData.pullbackHom A h)) hh)
    (hY₂ : DescentMor.mk (⟨(ε ≫ h) ≫ u, Y₂⟩ : DescentPairData (A.pullback (ε ≫ h)) B) =
      F (DescentMor.mk (DescentPairData.pullbackHom A (ε ≫ h))) hk) :
    DescentMor.mk (⟨(ε ≫ h) ≫ u, Y₂⟩ : DescentPairData (A.pullback (ε ≫ h)) B) =
      DescentMor.mk ((DescentPairData.pullbackComp A h ε (ε ≫ h) rfl).comp ⟨h ≫ u, Y₁⟩) := by
  rw [hY₂, ← family_congr F (pullbackComp_comp_pullbackHom A h ε (ε ≫ h) rfl) hk hk,
    hFcomp (DescentMor.mk (DescentPairData.pullbackComp A h ε (ε ≫ h) rfl))
      (DescentMor.mk (DescentPairData.pullbackHom A h)) hh hk, ← hY₁]
  rfl

/-- The local morphisms of fibres of two morphism data out of the pullbacks of `A` along `h` and
`ε ≫ h`, agreeing after restriction, are intertwined by the gluing isomorphisms. -/
private theorem descentMorLocal_iso_comp_of_agree {A B : DescentPair p J} {u : A.pt ⟶ B.pt}
    {V₁ Z V₀ : 𝒮} {h : V₁ ⟶ A.pt} (hhA : A.sieve.arrows h) (ε : Z ⟶ V₁)
    (hkA : A.sieve.arrows (ε ≫ h)) {g : V₁ ⟶ B.pt} (hg : B.sieve.arrows g) (pf : h ≫ u = g)
    (hg' : B.sieve.arrows (ε ≫ g)) (pf' : (ε ≫ h) ≫ u = ε ≫ g)
    (Y₁ : DescentPairHom (A.pullback h) B (h ≫ u))
    (Y₂ : DescentPairHom (A.pullback (ε ≫ h)) B ((ε ≫ h) ≫ u)) (γ : V₀ ⟶ Z)
    (hγk : Y₂.sieve.arrows γ) (hγε : Y₁.sieve.arrows (γ ≫ ε))
    (hag : ∀ {g₀ : V₀ ⟶ B.pt} (hg₀ : B.sieve.arrows g₀) (pfa : γ ≫ ((ε ≫ h) ≫ u) = g₀)
      (pfb : (γ ≫ ε) ≫ (h ≫ u) = g₀),
      Y₂.map γ hγk hg₀ pfa =
        eqToHom (A.datum.obj_congr (assoc γ ε h).symm (Y₂.le_dom_pullback hγk)
          (Y₁.le_dom_pullback hγε)) ≫ Y₁.map (γ ≫ ε) hγε hg₀ pfb) :
    (A.datum.iso hhA hkA (γ ≫ ε) γ (assoc γ ε h)).hom ≫
        descentMorLocal hkA hg' pf' Y₂ γ hγk ≫
        (B.datum.iso hg hg' (γ ≫ ε) γ (assoc γ ε g)).inv =
      descentMorLocal hhA hg pf Y₁ (γ ≫ ε) hγε := by
  have hb₁ : A.sieve.arrows ((γ ≫ ε) ≫ h) := Y₁.le_dom_pullback hγε
  have hb₂ : A.sieve.arrows (γ ≫ (ε ≫ h)) := Y₂.le_dom_pullback hγk
  have hc₁ : B.sieve.arrows ((γ ≫ ε) ≫ g) := B.sieve.downward_closed hg (γ ≫ ε)
  have hc₂ : B.sieve.arrows (γ ≫ (ε ≫ g)) := B.sieve.downward_closed hg' γ
  have eA : A.datum.obj (γ ≫ (ε ≫ h)) hb₂ = A.datum.obj ((γ ≫ ε) ≫ h) hb₁ :=
    A.datum.obj_congr (assoc γ ε h).symm hb₂ hb₁
  have eB : B.datum.obj (γ ≫ (ε ≫ g)) hc₂ = B.datum.obj ((γ ≫ ε) ≫ g) hc₁ :=
    B.datum.obj_congr (assoc γ ε g).symm hc₂ hc₁
  have hA3 : (A.datum.contract hkA γ hb₁ (assoc γ ε h).symm).inv ≫
      (A.datum.contract hkA γ hb₂ rfl).hom = eqToHom eA.symm := by
    rw [Iso.inv_comp_eq, ← A.datum.contract_hom_congr_tgt hkA γ hb₂ hb₁ rfl (assoc γ ε h).symm eA,
      assoc, eqToHom_trans, eqToHom_refl, comp_id]
  have hB3 : (B.datum.contract hg' γ hc₂ rfl).inv ≫
      (B.datum.contract hg' γ hc₁ (assoc γ ε g).symm).hom = eqToHom eB := by
    rw [← B.datum.contract_hom_congr_tgt hg' γ hc₂ hc₁ rfl (assoc γ ε g).symm eB,
      Iso.inv_hom_id_assoc]
  have hYmap : Y₂.map γ hγk hc₂ (show γ ≫ ((ε ≫ h) ≫ u) = γ ≫ (ε ≫ g) by rw [pf']) ≫
        eqToHom eB =
      eqToHom eA ≫ Y₁.map (γ ≫ ε) hγε hc₁
        (show (γ ≫ ε) ≫ (h ≫ u) = (γ ≫ ε) ≫ g by rw [pf]) := by
    rw [DescentPairHom.map_target_congr Y₂ γ hγk
      (show γ ≫ (ε ≫ g) = (γ ≫ ε) ≫ g from (assoc γ ε g).symm) hc₂ hc₁
      (show γ ≫ ((ε ≫ h) ≫ u) = γ ≫ (ε ≫ g) by rw [pf'])
      (show γ ≫ ((ε ≫ h) ≫ u) = (γ ≫ ε) ≫ g by rw [pf', assoc])]
    exact hag hc₁ (show γ ≫ ((ε ≫ h) ≫ u) = (γ ≫ ε) ≫ g by rw [pf', assoc])
      (show (γ ≫ ε) ≫ (h ≫ u) = (γ ≫ ε) ≫ g by rw [pf])
  rw [← A.datum.contract_hom_comp_contract_inv hhA hkA (γ ≫ ε) γ hb₁ rfl
      (assoc γ ε h).symm (assoc γ ε h),
    ← B.datum.contract_hom_comp_contract_inv' hg hg' (γ ≫ ε) γ hc₁ rfl
      (assoc γ ε g).symm (assoc γ ε g)]
  simp only [descentMorLocal, assoc]
  rw [reassoc_of% hA3, reassoc_of% hB3, reassoc_of% hYmap]
  simp

/-- **The glued morphisms of fibres of two morphism data out of the pullbacks of `A` along `h` and
`ε ≫ h`, related through `CategoryTheory.Functor.DescentPairData.pullbackComp`, are compatible
with restriction along `ε`.** -/
private theorem pullbackFiberHom_eq_of_mk_eq_pullbackComp_comp
    (hmor : ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y)
    {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {V₁ Z : 𝒮} {h : V₁ ⟶ A.pt}
    (hhA : A.sieve.arrows h) (ε : Z ⟶ V₁) (hkA : A.sieve.arrows (ε ≫ h)) {g : V₁ ⟶ B.pt}
    (hg : B.sieve.arrows g) (pf : h ≫ u = g) (hg' : B.sieve.arrows (ε ≫ g))
    (pf' : (ε ≫ h) ≫ u = ε ≫ g) {Y₁ : DescentPairHom (A.pullback h) B (h ≫ u)}
    {Y₂ : DescentPairHom (A.pullback (ε ≫ h)) B ((ε ≫ h) ≫ u)}
    (hY : DescentMor.mk (⟨(ε ≫ h) ≫ u, Y₂⟩ : DescentPairData (A.pullback (ε ≫ h)) B) =
      DescentMor.mk ((DescentPairData.pullbackComp A h ε (ε ≫ h) rfl).comp ⟨h ≫ u, Y₁⟩))
    {m₁ : A.datum.obj h hhA ⟶ B.datum.obj g hg}
    (hm₁ : ∀ ⦃W : 𝒮⦄ (δ : W ⟶ V₁) (hδ : Y₁.sieve.arrows δ),
      pullbackFiberHom m₁ δ = descentMorLocal hhA hg pf Y₁ δ hδ)
    {m₂ : A.datum.obj (ε ≫ h) hkA ⟶ B.datum.obj (ε ≫ g) hg'}
    (hm₂ : ∀ ⦃W : 𝒮⦄ (δ : W ⟶ Z) (hδ : Y₂.sieve.arrows δ),
      pullbackFiberHom m₂ δ = descentMorLocal hkA hg' pf' Y₂ δ hδ) :
    pullbackFiberHom m₁ ε =
      (A.datum.contract hhA ε hkA rfl).hom ≫ m₂ ≫ (B.datum.contract hg ε hg' rfl).inv := by
  obtain ⟨Tr, hTr, hle₁, hle₂, hagree⟩ := DescentPairHom.exists_sieve_map_eq_of_mk_eq hY
  refine eq_of_pullbackFiberHom_locally_eq p (hmor Z _ _) hTr ?_
  intro V₀ γ hγ
  have hγk : Y₂.sieve.arrows γ := hle₁ hγ
  have hγε : Y₁.sieve.arrows (γ ≫ ε) := hle₂ hγ
  have hP : pullbackFiberHom (pullbackFiberHom m₁ ε) γ =
      (pullbackFiberCompIso (A.datum.obj h hhA) ε γ).hom ≫
        descentMorLocal hhA hg pf Y₁ (γ ≫ ε) hγε ≫
        (pullbackFiberCompIso (B.datum.obj g hg) ε γ).inv := by
    rw [← hm₁ (γ ≫ ε) hγε, pullbackFiberHom_comp_base m₁ ε γ]
    simp
  have hQ : pullbackFiberHom ((A.datum.contract hhA ε hkA rfl).hom ≫ m₂ ≫
        (B.datum.contract hg ε hg' rfl).inv) γ =
      (pullbackFiberCompIso (A.datum.obj h hhA) ε γ).hom ≫
        ((A.datum.iso hhA hkA (γ ≫ ε) γ (assoc γ ε h)).hom ≫
          descentMorLocal hkA hg' pf' Y₂ γ hγk ≫
          (B.datum.iso hg hg' (γ ≫ ε) γ (assoc γ ε g)).inv) ≫
        (pullbackFiberCompIso (B.datum.obj g hg) ε γ).inv := by
    rw [pullbackFiberHom_comp, pullbackFiberHom_comp,
      A.datum.pullbackFiberHom_contract hhA ε hkA rfl γ, hm₂ γ hγk,
      B.datum.pullbackFiberHom_contract_inv hg ε hg' rfl γ]
    simp
  rw [hP, hQ, descentMorLocal_iso_comp_of_agree hhA ε hkA hg pf hg' pf' Y₁ Y₂ γ hγk hγε
    fun hg₀ pfa pfb ↦ hagree γ hγ hg₀ pfa pfb hγk hγε]

/-- The glued morphism of fibres at `ε ≫ h` is the value at `ε` of the morphism datum out of the
pullback along `h`. -/
private theorem eq_map_of_mk_eq_pullbackComp_comp
    (hmor : ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y)
    {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {V₁ Z : 𝒮} {h : V₁ ⟶ A.pt}
    (hhA : A.sieve.arrows h) (ε : Z ⟶ V₁) (hkA : A.sieve.arrows (ε ≫ h)) {g : V₁ ⟶ B.pt}
    (hg : B.sieve.arrows g) (pf : h ≫ u = g) (hg' : B.sieve.arrows (ε ≫ g))
    (pf' : (ε ≫ h) ≫ u = ε ≫ g) {Y₁ : DescentPairHom (A.pullback h) B (h ≫ u)}
    {Y₂ : DescentPairHom (A.pullback (ε ≫ h)) B ((ε ≫ h) ≫ u)}
    (hY : DescentMor.mk (⟨(ε ≫ h) ≫ u, Y₂⟩ : DescentPairData (A.pullback (ε ≫ h)) B) =
      DescentMor.mk ((DescentPairData.pullbackComp A h ε (ε ≫ h) rfl).comp ⟨h ≫ u, Y₁⟩))
    {m₁ : A.datum.obj h hhA ⟶ B.datum.obj g hg}
    (hm₁ : ∀ ⦃W : 𝒮⦄ (δ : W ⟶ V₁) (hδ : Y₁.sieve.arrows δ),
      pullbackFiberHom m₁ δ = descentMorLocal hhA hg pf Y₁ δ hδ)
    {m₂ : A.datum.obj (ε ≫ h) hkA ⟶ B.datum.obj (ε ≫ g) hg'}
    (hm₂ : ∀ ⦃W : 𝒮⦄ (δ : W ⟶ Z) (hδ : Y₂.sieve.arrows δ),
      pullbackFiberHom m₂ δ = descentMorLocal hkA hg' pf' Y₂ δ hδ)
    (hε : Y₁.sieve.arrows ε) :
    m₂ = Y₁.map ε hε hg' (show ε ≫ (h ≫ u) = ε ≫ g by rw [pf]) := by
  have h1 := pullbackFiberHom_eq_of_mk_eq_pullbackComp_comp hmor hhA ε hkA hg pf hg' pf' hY hm₁ hm₂
  rw [hm₁ ε hε] at h1
  have h2 : (A.datum.contract hhA ε hkA rfl).hom ≫ m₂ ≫ (B.datum.contract hg ε hg' rfl).inv =
      (A.datum.contract hhA ε hkA rfl).hom ≫
        Y₁.map ε hε hg' (show ε ≫ (h ≫ u) = ε ≫ g by rw [pf]) ≫
        (B.datum.contract hg ε hg' rfl).inv := h1.symm
  rwa [Iso.cancel_iso_hom_left, Iso.cancel_iso_inv_right] at h2

/-- A morphism datum out of `A` whose morphisms at the arrows `δ ≫ h` are those of a morphism
datum out of the pullback of `A` along `h` restricts to it along the canonical morphism out of
that pullback. -/
private theorem pullbackHom_comp_mk_eq_of_map_eq {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {V : 𝒮}
    {h : V ⟶ A.pt} (H : DescentPairHom A B u) (Y : DescentPairHom (A.pullback h) B (h ≫ u))
    (hHY : ∀ ⦃V₀ : 𝒮⦄ (δ : V₀ ⟶ V) (hδ₁ : Y.sieve.arrows δ) (hδ₂ : H.sieve.arrows (δ ≫ h))
      (hg₀ : B.sieve.arrows (δ ≫ h ≫ u)),
      H.map (δ ≫ h) hδ₂ hg₀ (assoc δ h u) = Y.map δ hδ₁ hg₀ rfl) :
    ((DescentMor.mk (DescentPairData.pullbackHom A h) : A.pullback h ⟶ A) ≫
        DescentMor.mk (⟨u, H⟩ : DescentPairData A B) : A.pullback h ⟶ B) =
      DescentMor.mk (⟨h ≫ u, Y⟩ : DescentPairData (A.pullback h) B) := by
  refine (DescentMor.mk_eq_iff _ _).mpr ⟨rfl, Y.sieve ⊓ H.sieve.pullback h,
    J.intersection_covering Y.sieve_mem (J.pullback_stable h H.sieve_mem), ?_, ?_, ?_⟩
  · intro V₀ δ hδ
    obtain ⟨hδ₁, hδ₂⟩ := (Sieve.inter_apply δ).1 hδ
    exact (Sieve.inter_apply δ).2
      ⟨(Sieve.pullback_apply _ _ _ _).mpr (Y.le_dom_pullback hδ₁), hδ₂⟩
  · intro V₀ δ hδ
    exact ((Sieve.inter_apply δ).1 hδ).1
  · intro V₀ δ hδ g₀ hg₀ pfa pfb
    obtain rfl := pfb
    obtain ⟨hδ₁, hδ₂⟩ := (Sieve.inter_apply δ).1 hδ
    rw [DescentPairData.comp_hom_map (DescentPairData.pullbackHom A h) ⟨u, H⟩ δ
        ((Sieve.pullback_apply _ _ _ _).mpr (Y.le_dom_pullback hδ₁)) hδ₂ hg₀
        (assoc δ h u) _ _,
      pullbackHom_map_eq_id, id_comp]
    exact hHY δ hδ₁ hδ₂ hg₀

/-- **A morphism of the third stage that agrees with a compatible family at the canonical morphisms
out of the pullbacks along the arrows of a covering sieve agrees with it everywhere**, as soon as
locally equal morphisms of `𝒳` are equal. -/
private theorem comp_eq_of_pullbackHom_comp_eq
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : DescentPair p J} {u : A.pt ⟶ B.pt} {S : Sieve A.pt}
    (F : ∀ {W : DescentPair p J} (Φ : W ⟶ A), S.arrows ((p.descentPairProj J).map Φ) → (W ⟶ B))
    (hFbase : ∀ {W : DescentPair p J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.descentPairProj J).map Φ)),
      (p.descentPairProj J).map (F Φ hΦ) = (p.descentPairProj J).map Φ ≫ u)
    (hFcomp : ∀ {W W' : DescentPair p J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
      (hΦ : S.arrows ((p.descentPairProj J).map Φ))
      (hΨΦ : S.arrows ((p.descentPairProj J).map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ)
    {T : Sieve A.pt} (hTmem : T ∈ J A.pt) (hTS : T ≤ S) (G : A ⟶ B)
    (hG : (p.descentPairProj J).map G = u)
    (hstep : ∀ (V : 𝒮) (h : V ⟶ A.pt) (hh : T.arrows h),
      (DescentMor.mk (DescentPairData.pullbackHom A h) : A.pullback h ⟶ A) ≫ G =
        F (DescentMor.mk (DescentPairData.pullbackHom A h)) (hTS _ hh)) :
    ∀ {W : DescentPair p J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.descentPairProj J).map Φ)),
      Φ ≫ G = F Φ hΦ := by
  intro W Φ hΦ
  refine (locallyEqual_descentPairProj_iff hsep (Φ ≫ G) (F Φ hΦ)).mp ⟨?_, ?_⟩
  · rw [Functor.map_comp, hFbase Φ hΦ, hG]
  refine ⟨T.pullback ((p.descentPairProj J).map Φ), J.pullback_stable _ hTmem, ?_⟩
  intro W'' ψ hψ
  have hkT : T.arrows ((p.descentPairProj J).map (ψ ≫ Φ)) := by
    rwa [Functor.map_comp]
  have hcart := isStronglyCartesian_pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ))
  obtain ⟨κ, ⟨-, hκ⟩, -⟩ := IsStronglyCartesian.universal_property (p.descentPairProj J)
    ((p.descentPairProj J).map (ψ ≫ Φ))
    (DescentMor.mk (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ))))
    (𝟙 W''.pt) ((p.descentPairProj J).map (ψ ≫ Φ)) (id_comp _).symm (ψ ≫ Φ)
  have hκS : S.arrows ((p.descentPairProj J).map (κ ≫
      DescentMor.mk (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ))))) := by
    rw [hκ]
    exact hTS _ hkT
  calc ψ ≫ Φ ≫ G
      = (κ ≫ DescentMor.mk
          (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ)))) ≫ G := by
        rw [hκ, assoc]
    _ = κ ≫ (DescentMor.mk
          (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ))) ≫ G) :=
        assoc _ _ _
    _ = κ ≫ F (DescentMor.mk
          (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ))))
            (hTS _ hkT) := by
        rw [hstep _ _ hkT]
    _ = F (κ ≫ DescentMor.mk
          (DescentPairData.pullbackHom A ((p.descentPairProj J).map (ψ ≫ Φ)))) hκS :=
        (hFcomp κ (DescentMor.mk (DescentPairData.pullbackHom A
          ((p.descentPairProj J).map (ψ ≫ Φ)))) (hTS _ hkT) hκS).symm
    _ = F (ψ ≫ Φ) (hTS _ hkT) := family_congr F hκ hκS (hTS _ hkT)
    _ = ψ ≫ F Φ hΦ := hFcomp ψ Φ hΦ (hTS _ hkT)

/-- **A family of morphisms of fibres indexed by a covering sieve and compatible with restriction
is compatible with the gluing isomorphisms of the two descent data.** -/
private theorem map_glue_of_pullbackFiberHom_eq {A B : DescentPair p J} {u : A.pt ⟶ B.pt}
    {T : Sieve A.pt} (hTA : T ≤ A.sieve)
    (m : ∀ (V : 𝒮) (h : V ⟶ A.pt) (hh : T.arrows h) (g : V ⟶ B.pt) (hg : B.sieve.arrows g),
      h ≫ u = g → (A.datum.obj h (hTA _ hh) ⟶ B.datum.obj g hg))
    (hstar : ∀ (V₁ Z : 𝒮) (h : V₁ ⟶ A.pt) (hh : T.arrows h) (ε : Z ⟶ V₁) (k : Z ⟶ A.pt)
      (hεk : ε ≫ h = k) (hk : T.arrows k) (g : V₁ ⟶ B.pt) (hg : B.sieve.arrows g)
      (pf : h ≫ u = g) (g' : Z ⟶ B.pt) (hg' : B.sieve.arrows g') (hεg : ε ≫ g = g')
      (pf' : k ≫ u = g'),
      pullbackFiberHom (m V₁ h hh g hg pf) ε =
        (A.datum.contract (hTA _ hh) ε (hTA _ hk) hεk).hom ≫ m Z k hk g' hg' pf' ≫
          (B.datum.contract hg ε hg' hεg).inv) :
    ∀ ⦃V W Z : 𝒮⦄ (f : V ⟶ A.pt) (hf : T.arrows f) (f' : W ⟶ A.pt)
      (hf' : T.arrows f') ⦃g : V ⟶ B.pt⦄ (hg : B.sieve.arrows g) (hq : f ≫ u = g)
      ⦃g' : W ⟶ B.pt⦄ (hg' : B.sieve.arrows g') (hq' : f' ≫ u = g')
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ f'),
      pullbackFiberHom (m V f hf g hg hq) ε ≫
          (B.datum.iso hg hg' ε ε' (by rw [← hq, ← hq', ← assoc, ← assoc, heq])).hom =
        (A.datum.iso (hTA _ hf) (hTA _ hf') ε ε' heq).hom ≫
          pullbackFiberHom (m W f' hf' g' hg' hq') ε' := by
  intro V W Z f hf f' hf' g hg hq g' hg' hq' ε ε' heq
  have hk : T.arrows (ε ≫ f) := T.downward_closed hf ε
  have hg₀ : B.sieve.arrows (ε ≫ g) := B.sieve.downward_closed hg ε
  have hεg' : ε' ≫ g' = ε ≫ g := by rw [← hq, ← hq', ← assoc, ← assoc, heq]
  have pf : (ε ≫ f) ≫ u = ε ≫ g := by rw [assoc, hq]
  rw [hstar V Z f hf ε (ε ≫ f) rfl hk g hg hq (ε ≫ g) hg₀ rfl pf,
    hstar W Z f' hf' ε' (ε ≫ f) heq.symm hk g' hg' hq' (ε ≫ g) hg₀ hεg' pf,
    ← A.datum.contract_hom_comp_contract_inv (hTA _ hf) (hTA _ hf') ε ε' (hTA _ hk) rfl
      heq.symm heq,
    ← B.datum.contract_hom_comp_contract_inv hg hg' ε ε' hg₀ rfl hεg' hεg'.symm]
  simp

/-- **The gluing half of the sheaf condition for the morphism presheaves of the third stage.** -/
theorem exists_amalgamation_descentPairProj
    (hmor : ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y)
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    {A B : DescentPair p J} (u : A.pt ⟶ B.pt) {S : Sieve A.pt} (hS : S ∈ J A.pt)
    (F : ∀ {W : DescentPair p J} (Φ : W ⟶ A), S.arrows ((p.descentPairProj J).map Φ) → (W ⟶ B))
    (hFbase : ∀ {W : DescentPair p J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.descentPairProj J).map Φ)),
      (p.descentPairProj J).map (F Φ hΦ) = (p.descentPairProj J).map Φ ≫ u)
    (hFcomp : ∀ {W W' : DescentPair p J} (Ψ : W' ⟶ W) (Φ : W ⟶ A)
      (hΦ : S.arrows ((p.descentPairProj J).map Φ))
      (hΨΦ : S.arrows ((p.descentPairProj J).map (Ψ ≫ Φ))), F (Ψ ≫ Φ) hΨΦ = Ψ ≫ F Φ hΦ) :
    ∃ G : A ⟶ B, (p.descentPairProj J).map G = u ∧
      ∀ {W : DescentPair p J} (Φ : W ⟶ A) (hΦ : S.arrows ((p.descentPairProj J).map Φ)),
        Φ ≫ G = F Φ hΦ := by
  have hex : ∀ (V : 𝒮) (h : V ⟶ A.pt) (hh : S.arrows h),
      ∃ Z : DescentPairHom (A.pullback h) B (h ≫ u),
        DescentMor.mk (⟨h ≫ u, Z⟩ : DescentPairData (A.pullback h) B) =
          F (DescentMor.mk (DescentPairData.pullbackHom A h)) hh :=
    fun _ h hh ↦ DescentMor.exists_hom_of_map_eq _
      (hFbase (DescentMor.mk (DescentPairData.pullbackHom A h)) hh)
  choose Y hY using hex
  set T : Sieve A.pt := S ⊓ (A.sieve ⊓ B.sieve.pullback u)
  have hTmem : T ∈ J A.pt := J.intersection_covering hS
    (J.intersection_covering A.sieve_mem (J.pullback_stable u B.sieve_mem))
  have hTS : T ≤ S := inf_le_left
  have hTA : T ≤ A.sieve := le_trans inf_le_right inf_le_left
  have hTB : T ≤ B.sieve.pullback u := le_trans inf_le_right inf_le_right
  choose m hm using fun (V : 𝒮) (h : V ⟶ A.pt) (hh : T.arrows h) (g : V ⟶ B.pt)
      (hg : B.sieve.arrows g) (pf : h ≫ u = g) ↦
    exists_fiberHom_of_descentPairHom hmor (hTA _ hh) hg pf (Y V h (hTS _ hh))
  have hstar : ∀ (V₁ Z : 𝒮) (h : V₁ ⟶ A.pt) (hh : T.arrows h) (ε : Z ⟶ V₁) (k : Z ⟶ A.pt)
      (hεk : ε ≫ h = k) (hk : T.arrows k) (g : V₁ ⟶ B.pt) (hg : B.sieve.arrows g)
      (pf : h ≫ u = g) (g' : Z ⟶ B.pt) (hg' : B.sieve.arrows g') (hεg : ε ≫ g = g')
      (pf' : k ≫ u = g'),
      pullbackFiberHom (m V₁ h hh g hg pf) ε =
        (A.datum.contract (hTA _ hh) ε (hTA _ hk) hεk).hom ≫ m Z k hk g' hg' pf' ≫
          (B.datum.contract hg ε hg' hεg).inv := by
    rintro V₁ Z h hh ε _ rfl hk g hg pf _ hg' rfl pf'
    exact pullbackFiberHom_eq_of_mk_eq_pullbackComp_comp hmor _ ε _ hg pf hg' pf'
      (mk_eq_pullbackComp_comp_of_compatible F hFcomp (hTS _ hh) ε (hTS _ hk)
        (hY V₁ h (hTS _ hh)) (hY Z (ε ≫ h) (hTS _ hk)))
      (hm V₁ h hh g hg pf) (hm Z _ hk _ hg' pf')
  refine ⟨DescentMor.mk ⟨u,
    { sieve := T
      sieve_mem := hTmem
      le_dom := hTA
      mem_cod := fun _ f hf ↦ hTB _ hf
      map := fun _ f hf _ hg pf ↦ m _ f hf _ hg pf
      map_glue := map_glue_of_pullbackFiberHom_eq hTA m hstar }⟩, rfl, ?_⟩
  refine comp_eq_of_pullbackHom_comp_eq hsep F hFbase hFcomp hTmem hTS _ (by exact rfl)
    fun V h hh ↦ ?_
  rw [← hY V h (hTS _ hh)]
  exact pullbackHom_comp_mk_eq_of_map_eq _ _ fun V₀ δ hδ₁ hδ₂ hg₀ ↦
    eq_map_of_mk_eq_pullbackComp_comp hmor (hTA _ hh) δ (hTA _ hδ₂) (g := h ≫ u) (hTB _ hh) rfl
      hg₀ (assoc δ h u) (mk_eq_pullbackComp_comp_of_compatible F hFcomp (hTS _ hh) δ
        (hTS _ hδ₂) (hY V h (hTS _ hh)) (hY V₀ (δ ≫ h) (hTS _ hδ₂)))
      (hm V h hh (h ≫ u) (hTB _ hh) rfl) (hm V₀ (δ ≫ h) hδ₂ _ hg₀ _) hδ₁

/-! ### Condition (2) of Stacks 026F for the third stage -/

/-- **Condition (2) of Stacks 026F for the third stage**: the morphism presheaves of
`CategoryTheory.Functor.descentPairProj` are sheaves, as soon as those of `p` are and its locally
equal morphisms are equal. The separatedness half is
`CategoryTheory.Functor.locallyEqual_descentPairProj_iff` and the gluing half is
`CategoryTheory.Functor.exists_amalgamation_descentPairProj`. -/
theorem isMorSheaf_descentPairProj
    (hmor : ∀ (U : 𝒮) (x y : p.Fiber U), IsMorSheaf p J U x y)
    (hsep : ∀ {x y : 𝒳} {a b : x ⟶ y}, p.LocallyEqual J a b → a = b)
    (U : 𝒮) (x y : (p.descentPairProj J).Fiber U) :
    IsMorSheaf (p.descentPairProj J) J U x y :=
  isMorSheaf_descentPairProj_of_amalgamation hsep (exists_amalgamation_descentPairProj hmor hsep)
    U x y

/-- **The morphism presheaves of the composite of the three stages are sheaves**, that is,
condition (2) of Stacks 026F holds for `CategoryTheory.Functor.stageThreeProj`. The first two
stages supply both hypotheses of
`CategoryTheory.Functor.isMorSheaf_descentPairProj`:
`CategoryTheory.Functor.isMorSheaf_stageTwoProj` and
`CategoryTheory.Functor.locallyEqual_stageTwoProj_iff`. -/
theorem isMorSheaf_stageThreeProj (q : 𝒳 ⥤ 𝒮) [q.IsFibered] (J : GrothendieckTopology 𝒮) (U : 𝒮)
    (x y : (q.stageThreeProj J).Fiber U) : IsMorSheaf (q.stageThreeProj J) J U x y :=
  isMorSheaf_descentPairProj (isMorSheaf_stageTwoProj q J)
    (fun hab ↦ (locallyEqual_stageTwoProj_iff _ _).mp hab) U x y

end CategoryTheory.Functor
