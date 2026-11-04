module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Operations
public import StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.SymQuotientProjection

/-!
# The directed system of finitely presented quotients `Sym(ℱᵢ)/ℐ`

Let `X` be a scheme, `𝒜` a quasi-coherent sheaf of commutative `𝒪_X`-algebras and
`D : I ⥤ 𝒪_X-Mod` a system of quasi-coherent modules over a partial order `I`, with maps
`φᵢ : ℱᵢ ⟶ 𝒜`. This file builds the index poset of [Stacks, Tag 05JS],

`(i, ℐ)` with `i : I` and `ℐ` a finite type quasi-coherent ideal of `𝐕(ℱᵢ)` killed by
`pᵢ : Spec_X(𝒜) ⟶ 𝐕(ℱᵢ)`,

ordered by `(i, ℐ) ≤ (j, 𝒥)` iff `i ≤ j` and `ℐ ≤ 𝒥.map 𝐕(ℱⱼ ⟶ ℱᵢ)`, together with the functor
`(i, ℐ) ↦ Sym(ℱᵢ)/ℐ` into the algebra sheaves and its cocone over `𝒜`.

## Main definitions

* `Stacks.SymQuotientSystem.Index`: **the index poset**, and `IndexLe` its order.
* `Stacks.SymQuotientSystem.system`: **the functor `(i, ℐ) ↦ Sym(ℱᵢ)/ℐ`.**
* `Stacks.SymQuotientSystem.cocone`: **the cocone of the system over `𝒜`.**

## Main results

* `Stacks.SymQuotientSystem.indexPartialOrder`, `indexNonempty` and `indexIsDirected`: the index
  is a nonempty directed partial order. Directedness is
  `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_map` on the ideal component, at the two
  transition maps into a common later index.
* `Stacks.SymQuotientSystem.isQuasicoherent_system_obj` and
  `isOfFinitePresentation_system_obj`: **every member of the system is quasi-coherent, and of
  finite presentation when the modules of `D` are.**

## Implementation notes

**Why the kernel condition is part of the index.** The map `Sym(ℱᵢ)/ℐ ⟶ 𝒜` exists only once `ℐ`
is killed by `pᵢ`, so carrying `ℐ ≤ pᵢ.ker` in the index is what makes the cocone definable at
all. Directedness survives it: the join witness is `ℐ.comap 𝐕(f) ⊔ 𝒥.comap 𝐕(g)`, and
`AlgebraicGeometry.Scheme.IdealSheafData.map_ker` together with the Galois connection
`AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le` turns `ℐ ≤ pᵢ.ker` into
`ℐ.comap 𝐕(f) ≤ p_k.ker`, because `pᵢ` *is* `p_k` followed by `𝐕(f)`
(`Stacks.SymQuotientSystem.proj_comp`).

**Antisymmetry.** The second component of the index lives over the first, so antisymmetry has to
substitute the equality of the first components before comparing the ideals; after the
substitution the two transition maps are identities
(`Stacks.SymQuotientSystem.vectorBundleMap_homOfLE_refl`) and the comparison is antisymmetry in
`AlgebraicGeometry.Scheme.IdealSheafData`.

**The order is an existential.** `IndexLe a b` is `∃ h : a.idx ≤ b.idx, …`, and the body depends
on `h` only through `CategoryTheory.homOfLE h`; since `a.idx ≤ b.idx` is a proposition, any two
witnesses are equal, so `IndexLe.idx` and `IndexLe.ideal` recover both components with no choice.

**Everything is written at one spelling.** The transition morphisms appear throughout as
`Stacks.SymQuotientAlgebra.symQuotientAlgebraMap` applied to `D.map (homOfLE …)`, never behind
an abbreviation of either. A statement that mixes an abbreviation with the morphism it
abbreviates makes the kernel compare two compositions of algebra sheaves by evaluating them,
which unfolds the glueing that builds the relative spectrum and does not terminate within
budget; that is also why the family `p` is abstract.

**Functoriality by substitution.** `Stacks.SymQuotientAlgebra.symQuotientAlgebraMap_id` and
`symQuotientAlgebraMap_comp` are stated for a literal identity resp. a literal composite of
module maps, while the functor laws present `D.map` of an identity resp. of a composite of
order-theoretic homs. The two are bridged by `symQuotientAlgebraMap_eq_id` and
`symQuotientAlgebraMap_eq_comp`, which generalize the module map and substitute; the hypothesis
`h` of the transition morphism depends on it, so a rewrite would not be type-correct.

**No `@[stacks]` attribute.** The tag is the colimit presentation, which is assembled in
`StacksFrontier.AlgebraicGeometry.QcohAlgebraFPColimit.Main`.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AffineAlgebraEquivalence Stacks.AlgebraicGeometry.FiniteTypeDominating
open Stacks.SymQuotientAlgebra

universe u

namespace Stacks.SymQuotientSystem

variable {X : Scheme.{u}}

/-! ### Transition morphisms of quotients, by substitution -/

section Substitution

variable {E E' E'' : SheafOfModules.{u} X.ringCatSheaf}
  [E.IsQuasicoherent] [E'.IsQuasicoherent] [E''.IsQuasicoherent]

/-- The transition morphism of quotients attached to a module map that *is* the identity is the
identity. This is `Stacks.SymQuotientAlgebra.symQuotientAlgebraMap_id` with the module map
generalized, so that it can be substituted. -/
theorem symQuotientAlgebraMap_eq_id (g : E ⟶ E) (hg : g = 𝟙 E)
    (J : (Scheme.Modules.vectorBundle X E).IdealSheafData)
    (h : J ≤ J.map (Scheme.Modules.vectorBundleMap X g).left) :
    symQuotientAlgebraMap E E g J J h =
      𝟙 (pushforwardAlgebra (symQuotientOver E J).hom) := by
  subst hg
  exact symQuotientAlgebraMap_id E J h

/-- The transition morphism of quotients attached to a module map that *is* a composite is the
composite of the transition morphisms. This is
`Stacks.SymQuotientAlgebra.symQuotientAlgebraMap_comp` with the module map generalized. -/
theorem symQuotientAlgebraMap_eq_comp (f : E ⟶ E') (g : E' ⟶ E'') (fg : E ⟶ E'')
    (hfg : fg = f ≫ g) (J : (Scheme.Modules.vectorBundle X E).IdealSheafData)
    (J' : (Scheme.Modules.vectorBundle X E').IdealSheafData)
    (J'' : (Scheme.Modules.vectorBundle X E'').IdealSheafData)
    (hf : J ≤ J'.map (Scheme.Modules.vectorBundleMap X f).left)
    (hg : J' ≤ J''.map (Scheme.Modules.vectorBundleMap X g).left)
    (hfg' : J ≤ J''.map (Scheme.Modules.vectorBundleMap X fg).left) :
    symQuotientAlgebraMap E E'' fg J J'' hfg' =
      symQuotientAlgebraMap E E' f J J' hf ≫ symQuotientAlgebraMap E' E'' g J' J'' hg := by
  subst hfg
  exact symQuotientAlgebraMap_comp E E' E'' f g J J' J'' hf hg hfg'

/-- The transition morphism of closed subschemes attached to a module map that *is* the identity
is the identity. -/
theorem symQuotientOverMap_eq_id (g : E ⟶ E) (hg : g = 𝟙 E)
    (J : (Scheme.Modules.vectorBundle X E).IdealSheafData)
    (h : J ≤ J.map (Scheme.Modules.vectorBundleMap X g).left) :
    symQuotientOverMap E E g J J h = 𝟙 (symQuotientOver E J) := by
  subst hg
  exact symQuotientOverMap_id E J h

/-- The transition morphism of closed subschemes attached to a module map that *is* a composite
is the composite of the transition morphisms, contravariantly. -/
theorem symQuotientOverMap_eq_comp (f : E ⟶ E') (g : E' ⟶ E'') (fg : E ⟶ E'')
    (hfg : fg = f ≫ g) (J : (Scheme.Modules.vectorBundle X E).IdealSheafData)
    (J' : (Scheme.Modules.vectorBundle X E').IdealSheafData)
    (J'' : (Scheme.Modules.vectorBundle X E'').IdealSheafData)
    (hf : J ≤ J'.map (Scheme.Modules.vectorBundleMap X f).left)
    (hg : J' ≤ J''.map (Scheme.Modules.vectorBundleMap X g).left)
    (hfg' : J ≤ J''.map (Scheme.Modules.vectorBundleMap X fg).left) :
    symQuotientOverMap E E'' fg J J'' hfg' =
      symQuotientOverMap E' E'' g J' J'' hg ≫ symQuotientOverMap E E' f J J' hf := by
  subst hfg
  exact symQuotientOverMap_comp E E' E'' f g J J' J'' hf hg hfg'

/-- The morphism of algebra sheaves out of `Sym(ℱ)/ℐ` depends on the morphism into `𝐕(ℱ)` only
through its value, the containment hypothesis being a proposition. -/
theorem quotientAlgebraLift_congr (J : (Scheme.Modules.vectorBundle X E).IdealSheafData)
    {Y : Over X} (q q' : Y ⟶ Scheme.Modules.vectorBundleOver X (F := E)) (hqq' : q = q')
    (h : J ≤ q.left.ker) (h' : J ≤ q'.left.ker) :
    quotientAlgebraLift E J q h = quotientAlgebraLift E J q' h' := by
  subst hqq'
  rfl

end Substitution

/-! ### The index poset -/

section Index

variable {I : Type u} [PartialOrder I] {D : I ⥤ SheafOfModules.{u} X.ringCatSheaf}
  [∀ i, (D.obj i).IsQuasicoherent] {Y : Over X}
  (p : ∀ i : I, Y ⟶ Scheme.Modules.vectorBundleOver X (F := D.obj i))

/-- **The index set of [Stacks, Tag 05JS]**: a stage `i` of the system of modules together with a
finite type quasi-coherent sheaf of ideals on the vector bundle `𝐕(ℱᵢ)` which is killed by the
morphism `pᵢ : Y ⟶ 𝐕(ℱᵢ)`. The attached member of the directed system is `Sym(ℱᵢ)/ℐ`.

The family `p` is left abstract: in the application it is the family of projections of
`Spec_X(𝒜)` to the vector bundles, whose values are glued morphisms, and keeping it opaque is
what stops the kernel from evaluating that glueing while checking the functor laws below. -/
structure Index where
  /-- The stage of the system of modules. -/
  idx : I
  /-- A quasi-coherent sheaf of ideals on the vector bundle of that stage. -/
  ideal : (Scheme.Modules.vectorBundle X (D.obj idx)).IdealSheafData
  /-- It is of finite type, which is what makes the quotient of finite presentation. -/
  isFiniteType : ideal.IsFiniteType
  /-- It is killed by `pᵢ`, which is what makes the quotient map to the target. -/
  le_ker : ideal ≤ (p idx).left.ker

/-- **The order on the index**: the stages are ordered in `I`, and the ideal of the smaller
index is contained in the inverse image of the ideal of the larger one along the transition map
of vector bundles.

The body depends on the witness `h` only through `CategoryTheory.homOfLE h`, and `a.idx ≤ b.idx`
is a proposition, so nothing is chosen. -/
def IndexLe (a b : Index p) : Prop :=
  ∃ h : a.idx ≤ b.idx,
    a.ideal ≤ b.ideal.map (Scheme.Modules.vectorBundleMap X (D.map (homOfLE h))).left

/-- The first component of the order. -/
theorem IndexLe.idx {a b : Index p} (h : IndexLe p a b) : a.idx ≤ b.idx :=
  h.elim fun hij _ => hij

/-- The second component of the order, at the witness produced by `IndexLe.idx`. -/
theorem IndexLe.ideal {a b : Index p} (h : IndexLe p a b) :
    a.ideal ≤
      b.ideal.map
        (Scheme.Modules.vectorBundleMap X (D.map (homOfLE (IndexLe.idx p h)))).left :=
  h.elim fun _ hI => hI

/-- The inverse image along the transition map at a reflexivity proof is the identity. -/
theorem map_vectorBundleMap_refl {i : I} (h : i ≤ i)
    (J : (Scheme.Modules.vectorBundle X (D.obj i)).IdealSheafData) :
    J.map (Scheme.Modules.vectorBundleMap X (D.map (homOfLE h))).left = J := by
  rw [vectorBundleMap_homOfLE_refl]
  exact Scheme.IdealSheafData.map_id J

/-- Reflexivity: the transition map at a reflexivity proof is the identity. -/
theorem indexLe_refl (a : Index p) : IndexLe p a a :=
  ⟨le_refl _, by rw [map_vectorBundleMap_refl]⟩

/-- Transitivity: the transition maps compose, and so do the inverse images. -/
theorem indexLe_trans {a b c : Index p} (hab : IndexLe p a b) (hbc : IndexLe p b c) :
    IndexLe p a c := by
  refine ⟨(IndexLe.idx p hab).trans (IndexLe.idx p hbc), ?_⟩
  refine (IndexLe.ideal p hab).trans ?_
  refine (Scheme.IdealSheafData.map_mono _ (IndexLe.ideal p hbc)).trans ?_
  rw [vectorBundleMap_homOfLE_trans (D := D) (IndexLe.idx p hab) (IndexLe.idx p hbc)
    ((IndexLe.idx p hab).trans (IndexLe.idx p hbc)), Over.comp_left,
    Scheme.IdealSheafData.map_comp]

/-- Antisymmetry. The equality of the stages is substituted first, after which the two transition
maps are identities. -/
theorem indexLe_antisymm {a b : Index p} (hab : IndexLe p a b) (hba : IndexLe p b a) : a = b := by
  obtain ⟨i, Ia, hIa, hka⟩ := a
  obtain ⟨j, Ib, hIb, hkb⟩ := b
  have hij : i = j := le_antisymm (IndexLe.idx p hab) (IndexLe.idx p hba)
  subst hij
  have hI : Ia = Ib := le_antisymm
    ((IndexLe.ideal p hab).trans (map_vectorBundleMap_refl _ _).le)
    ((IndexLe.ideal p hba).trans (map_vectorBundleMap_refl _ _).le)
  subst hI
  rfl

/-- **The index is a partial order.** -/
instance indexPartialOrder : PartialOrder (Index p) where
  le := IndexLe p
  le_refl := indexLe_refl p
  le_trans _ _ _ := indexLe_trans p
  le_antisymm _ _ := indexLe_antisymm p

/-- The order on the index, by its two components. -/
theorem Index.le_mk {a b : Index p} (h : a.idx ≤ b.idx)
    (hI : a.ideal ≤
      b.ideal.map (Scheme.Modules.vectorBundleMap X (D.map (homOfLE h))).left) :
    a ≤ b :=
  ⟨h, hI⟩

/-- **The index is nonempty**: the zero sheaf of ideals is of finite type and is killed by every
morphism. -/
instance indexNonempty [Nonempty I] : Nonempty (Index p) :=
  ⟨⟨Classical.arbitrary I, ⊥, Stacks.FiniteTypeIdealSheaf.isFiniteType_bot, bot_le⟩⟩

/-- **The index is directed.** Given two indices, take a common later stage `k` of `I`; the join
of the inverse images of the two ideals along the transition maps into `𝐕(ℱ_k)` is of finite
type, dominates both, and is killed by `p_k` because each of the two ideals is killed by its own
`pᵢ` and the family `p` is compatible with the transition maps. -/
theorem indexIsDirected [IsDirected I (· ≤ ·)]
    (hp : ∀ (i j : I) (h : i ≤ j),
      p j ≫ Scheme.Modules.vectorBundleMap X (D.map (homOfLE h)) = p i) :
    IsDirected (Index p) (· ≤ ·) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.idx b.idx
  have hker : ∀ (c : Index p) (hck : c.idx ≤ k),
      c.ideal.comap (Scheme.Modules.vectorBundleMap X (D.map (homOfLE hck))).left ≤
        (p k).left.ker := by
    intro c hck
    refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
    rw [Scheme.IdealSheafData.map_ker]
    have hpre : (p k).left ≫
        (Scheme.Modules.vectorBundleMap X (D.map (homOfLE hck))).left = (p c.idx).left := by
      rw [← Over.comp_left, hp _ _ hck]
    rw [hpre]
    exact c.le_ker
  refine ⟨⟨k, a.ideal.comap (Scheme.Modules.vectorBundleMap X (D.map (homOfLE hak))).left ⊔
      b.ideal.comap (Scheme.Modules.vectorBundleMap X (D.map (homOfLE hbk))).left,
    Stacks.FiniteTypeIdealSheaf.isFiniteType_comap_sup_comap _ _ a.isFiniteType b.isFiniteType,
    sup_le (hker a hak) (hker b hbk)⟩, Index.le_mk p hak ?_, Index.le_mk p hbk ?_⟩
  · exact Stacks.FiniteTypeIdealSheaf.le_map_comap_sup_comap_left _ _
  · exact Stacks.FiniteTypeIdealSheaf.le_map_comap_sup_comap_right _ _

/-! ### The system -/

/-- **The transition morphism of closed subschemes at a reflexivity proof is the identity.** -/
theorem symQuotientOverMap_index_refl (a : Index p) (h : a ≤ a) :
    symQuotientOverMap (D.obj a.idx) (D.obj a.idx)
        (D.map (homOfLE (IndexLe.idx p h))) a.ideal a.ideal (IndexLe.ideal p h) =
      𝟙 (symQuotientOver (D.obj a.idx) a.ideal) :=
  symQuotientOverMap_eq_id (D.map (homOfLE (IndexLe.idx p h)))
    ((congrArg D.map (Subsingleton.elim (homOfLE (IndexLe.idx p h)) (𝟙 a.idx))).trans
      (D.map_id a.idx)) a.ideal (IndexLe.ideal p h)

/-- **The transition morphisms of closed subschemes compose**, contravariantly. -/
theorem symQuotientOverMap_index_trans {a b c : Index p} (hab : a ≤ b) (hbc : b ≤ c)
    (hac : a ≤ c) :
    symQuotientOverMap (D.obj a.idx) (D.obj c.idx)
        (D.map (homOfLE (IndexLe.idx p hac))) a.ideal c.ideal (IndexLe.ideal p hac) =
      symQuotientOverMap (D.obj b.idx) (D.obj c.idx)
          (D.map (homOfLE (IndexLe.idx p hbc))) b.ideal c.ideal (IndexLe.ideal p hbc) ≫
        symQuotientOverMap (D.obj a.idx) (D.obj b.idx)
          (D.map (homOfLE (IndexLe.idx p hab))) a.ideal b.ideal (IndexLe.ideal p hab) :=
  symQuotientOverMap_eq_comp (D.map (homOfLE (IndexLe.idx p hab)))
    (D.map (homOfLE (IndexLe.idx p hbc))) (D.map (homOfLE (IndexLe.idx p hac)))
    ((congrArg D.map (Subsingleton.elim (homOfLE (IndexLe.idx p hac))
      (homOfLE (IndexLe.idx p hab) ≫ homOfLE (IndexLe.idx p hbc)))).trans (D.map_comp _ _))
    a.ideal b.ideal c.ideal (IndexLe.ideal p hab) (IndexLe.ideal p hbc) (IndexLe.ideal p hac)

/-- **The directed system of closed subschemes**: the functor carrying `(i, ℐ)` to the closed
subscheme `𝐙(ℐ) ⊆ 𝐕(ℱᵢ)` as a scheme over `X`, contravariantly.

The system of algebra sheaves is obtained from this one by pushing forward, which is what keeps
the functor laws cheap: they are the laws of `Stacks.SymQuotientAlgebra.symQuotientOverMap`,
proved by cancelling the closed immersion, and no law about `pushforwardAlgebra` is ever
stated. -/
def systemOver : Index p ⥤ (Over X)ᵒᵖ where
  obj a := op (symQuotientOver (D.obj a.idx) a.ideal)
  map {a b} h := Quiver.Hom.op (symQuotientOverMap (D.obj a.idx) (D.obj b.idx)
    (D.map (homOfLE (IndexLe.idx p (leOfHom h)))) a.ideal b.ideal
    (IndexLe.ideal p (leOfHom h)))
  map_id a := congrArg Quiver.Hom.op (symQuotientOverMap_index_refl p a (leOfHom (𝟙 a)))
  map_comp f g :=
    congrArg Quiver.Hom.op
      (symQuotientOverMap_index_trans p (leOfHom f) (leOfHom g) (leOfHom (f ≫ g)))

/-- **The directed system of [Stacks, Tag 05JS]**: the functor carrying `(i, ℐ)` to the
quasi-coherent algebra `Sym(ℱᵢ)/ℐ`, namely the pushed-forward structure sheaf of
`𝐙(ℐ) ⊆ 𝐕(ℱᵢ)`. -/
def system : Index p ⥤ X.QuasicoherentAlgebra :=
  systemOver p ⋙ pushforwardAlgebraFunctor X

/-- The member of the system at an index, by definition. -/
theorem system_obj (a : Index p) :
    (system p).obj a = pushforwardAlgebra (symQuotientOver (D.obj a.idx) a.ideal).hom :=
  rfl

/-- The transition morphism of the system, by definition. -/
theorem system_map {a b : Index p} (h : a ⟶ b) :
    (system p).map h = symQuotientAlgebraMap (D.obj a.idx) (D.obj b.idx)
      (D.map (homOfLE (IndexLe.idx p (leOfHom h)))) a.ideal b.ideal
      (IndexLe.ideal p (leOfHom h)) :=
  rfl

/-! ### The two conditions on the members -/

/-- **Every member of the system is quasi-coherent.** -/
theorem isQuasicoherent_system_obj (a : Index p) :
    Scheme.QuasicoherentAlgebra.IsQuasicoherent ((system p).obj a) :=
  isQuasicoherent_symQuotientAlgebra (D.obj a.idx) a.ideal

/-- **Every member of the system is of finite presentation**, when the modules of `D` are of
finite presentation: `Sym(ℱᵢ)` is then of finite presentation over `X` and `ℐ` is of finite
type. -/
theorem isOfFinitePresentation_system_obj [∀ i, (D.obj i).IsFinitePresentation] (a : Index p) :
    Scheme.QuasicoherentAlgebra.IsOfFinitePresentation ((system p).obj a) :=
  isOfFinitePresentation_symQuotientAlgebra (D.obj a.idx) a.ideal a.isFiniteType

/-! ### The cocone -/

variable (𝒜 : X.QuasicoherentAlgebra) (e : pushforwardAlgebra Y.hom ≅ 𝒜)

/-- **The component of the cocone at an index**: the morphism of algebra sheaves
`Sym(ℱᵢ)/ℐ ⟶ 𝒜` obtained by factoring `pᵢ` through the closed subscheme `𝐙(ℐ)` and then
identifying the pushed-forward structure sheaf of `Y` with `𝒜`. -/
def coconeApp (a : Index p) :
    pushforwardAlgebra (symQuotientOver (D.obj a.idx) a.ideal).hom ⟶ 𝒜 :=
  quotientAlgebraLift (D.obj a.idx) a.ideal (p a.idx) a.le_ker ≫ e.hom

/-- **The cocone of the system over `𝒜`.** Naturality is
`Stacks.SymQuotientAlgebra.quotientAlgebraLift_comp` together with the compatibility of the
family `p` with the transition maps. -/
def cocone (hp : ∀ (i j : I) (h : i ≤ j),
    p j ≫ Scheme.Modules.vectorBundleMap X (D.map (homOfLE h)) = p i) :
    system p ⟶ (Functor.const (Index p)).obj 𝒜 where
  app a := coconeApp p 𝒜 e a
  naturality a b h := by
    have hI : a.ideal ≤
        (p b.idx ≫ Scheme.Modules.vectorBundleMap X
          (D.map (homOfLE (IndexLe.idx p (leOfHom h))))).left.ker := by
      rw [hp _ _ (IndexLe.idx p (leOfHom h))]
      exact a.le_ker
    have key : symQuotientAlgebraMap (D.obj a.idx) (D.obj b.idx)
          (D.map (homOfLE (IndexLe.idx p (leOfHom h)))) a.ideal b.ideal
          (IndexLe.ideal p (leOfHom h)) ≫
        quotientAlgebraLift (D.obj b.idx) b.ideal (p b.idx) b.le_ker =
          quotientAlgebraLift (D.obj a.idx) a.ideal (p a.idx) a.le_ker :=
      (quotientAlgebraLift_comp (D.obj a.idx) (D.obj b.idx)
          (D.map (homOfLE (IndexLe.idx p (leOfHom h)))) a.ideal b.ideal
          (p b.idx) b.le_ker hI (IndexLe.ideal p (leOfHom h))).trans
        (quotientAlgebraLift_congr a.ideal _ (p a.idx)
          (hp _ _ (IndexLe.idx p (leOfHom h))) hI a.le_ker)
    refine Eq.trans ?_ (Category.comp_id (coconeApp p 𝒜 e a)).symm
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ e.hom) key)

end Index

end Stacks.SymQuotientSystem

end
