module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic

/-!
# Sections near a closed subscheme and the completion functor on neighbourhoods

Let `Y ⊆ X` be a closed subscheme of a Noetherian scheme, let `Y_n ⊆ X` be its infinitesimal
neighbourhoods, and let `𝒱` be the open subschemes of `X` containing `Y`, ordered by reverse
inclusion. Stacks 0EK2 compares four conditions:

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` carries an ample invertible module `L` and `colim_𝒱 Γ(V, L^{⊗ m}) → lim Γ(Y_n,
   L^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`;
3. `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism for every `V ∈ 𝒱`
   and every finite locally free `𝒪_V`-module `ℰ`;
4. the completion functor `colim_𝒱 Coh(𝒪_V) → Coh(X, I)` is fully faithful on the full
   subcategory of finite locally free objects,

and asserts (1) ⇒ (2) ⇒ (3) ⇒ (4) and (4) ⇒ (3). This file sets up the colimit side of the
comparison and proves the first implication.

The colimit over `𝒱` is spelled out elementwise rather than built as a categorical colimit:
since `𝒱` is directed, a map out of it is an isomorphism exactly when every compatible family of
sections on the `Y_n` comes from a section on some neighbourhood, and two sections on
neighbourhoods inducing the same family agree after shrinking the neighbourhood. These are the
two clauses of `Stacks.Algebraization.IsNeighbourhoodSectionsComplete`. The limit side is a
compatible family of sections of the pullbacks along the structure morphisms of the infinitesimal
neighbourhoods.

## Main definitions

* `AlgebraicGeometry.pullbackSectionsAt` — the pullback map on sections over an open whose
  preimage is everything; the case of the whole space is
  `AlgebraicGeometry.pullbackGlobalSections`.
* `Stacks.Algebraization.neighbourhoodSections` — restriction of a section over an open
  neighbourhood of a closed subscheme to the `n`-th infinitesimal neighbourhood.
* `Stacks.Algebraization.IsNeighbourhoodSectionsComplete` — the comparison occurring in
  conditions (1)–(3) above, for a fixed module: the colimit of the sections over the open
  neighbourhoods is the limit of the sections on the infinitesimal neighbourhoods.

## Main results

* `Stacks.Algebraization.range_nthInfinitesimalNeighbourhoodι` — an infinitesimal neighbourhood of
  a closed immersion has the same image as the immersion itself.
* `AlgebraicGeometry.pullbackSectionsAt_natural` and
  `AlgebraicGeometry.pullbackSectionsAt_restrict` — the section map is natural in the module and
  compatible with shrinking the open.
* `Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_iso` — neighbourhood section
  completeness depends only on the isomorphism class of the module.
* `Stacks.Algebraization.quasiAffine_neighbourhoodSectionsComplete_implies_amplePower` —
  condition (1) implies condition (2).

## References

* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 01QE](https://stacks.math.columbia.edu/tag/01QE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Two commuting squares sharing an edge paste to one. -/
private lemma pasteSquare {C : Type*} [Category C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (u : X₁ ⟶ X₂) (r : X₂ ⟶ X₃) (d : X₁ ⟶ Y₁) (p : X₂ ⟶ Y₂) (v : Y₁ ⟶ Y₂) (q : Y₂ ⟶ Y₃)
    (c : X₃ ⟶ Y₃) (h₁ : r ≫ c = p ≫ q) (h₂ : u ≫ p = d ≫ v) :
    (u ≫ r) ≫ c = d ≫ v ≫ q := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]

variable {W Y : Scheme.{u}} (f : W ⟶ Y)

/-- The pullback map from the sections of a module over an open whose preimage is everything to
the global sections of its pullback. -/
public def pullbackSectionsAt (F : Y.Modules) {V : Y.Opens} (hV : f ⁻¹ᵁ V = ⊤) :
    Γ(F, V) ⟶ Γ((Scheme.Modules.pullback f).obj F, ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V ≫
    ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom hV.symm).op

/-- Over the whole space the section map is the canonical map on global sections. -/
public theorem pullbackSectionsAt_top (F : Y.Modules) :
    pullbackSectionsAt f F (Opens.map_top f.base) =
      pullbackGlobalSections f F :=
  rfl

/-- Naturality of `pullbackSectionsAt` in the module, as a square of maps on sections. -/
public theorem pullbackSectionsAt_naturality_app {F G : Y.Modules} (φ : F ⟶ G) {V : Y.Opens}
    (hV : f ⁻¹ᵁ V = ⊤) :
    pullbackSectionsAt f F hV ≫ ((Scheme.Modules.pullback f).map φ).app ⊤ =
      φ.app V ≫ pullbackSectionsAt f G hV := by
  have h₁ : ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom hV.symm).op ≫
        ((Scheme.Modules.pullback f).map φ).app ⊤ =
      ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map φ)).app V ≫
        ((Scheme.Modules.pullback f).obj G).presheaf.map (eqToHom hV.symm).op :=
    ((Scheme.Modules.pullback f).map φ).mapPresheaf.naturality _
  have h₂ : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V ≫
        ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map φ)).app V =
      φ.app V ≫ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G).app V :=
    congrArg (fun χ => Scheme.Modules.Hom.app χ V)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality φ)
  exact pasteSquare _ _ _ _ _ _ _ h₁ h₂

/-- Pulling back sections over a neighbourhood commutes with a morphism of modules. -/
public theorem pullbackSectionsAt_natural {F G : Y.Modules} (φ : F ⟶ G) {V : Y.Opens}
    (hV : f ⁻¹ᵁ V = ⊤) (s : Γ(F, V)) :
    pullbackSectionsAt f G hV (φ.app V s) =
      ((Scheme.Modules.pullback f).map φ).app ⊤ (pullbackSectionsAt f F hV s) :=
  (ConcreteCategory.comp_apply (φ.app V) (pullbackSectionsAt f G hV) s).symm.trans
    ((ConcreteCategory.congr_hom (pullbackSectionsAt_naturality_app f φ hV) s).symm.trans
      (ConcreteCategory.comp_apply (pullbackSectionsAt f F hV)
        (((Scheme.Modules.pullback f).map φ).app ⊤) s))

/-- Shrinking the open does not change the pulled-back section. -/
public theorem pullbackSectionsAt_restrict (F : Y.Modules) {V V' : Y.Opens} (h : V' ≤ V)
    (hV : f ⁻¹ᵁ V = ⊤) (hV' : f ⁻¹ᵁ V' = ⊤) (s : Γ(F, V)) :
    pullbackSectionsAt f F hV' (F.presheaf.map (homOfLE h).op s) =
      pullbackSectionsAt f F hV s := by
  have hnat := NatTrans.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).mapPresheaf (homOfLE h).op s
  have key : ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V'
        (F.presheaf.map (homOfLE h).op s) =
      ((Scheme.Modules.pullback f).obj F).presheaf.map
        ((Opens.map f.base).map (homOfLE h)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V s) := hnat
  have hcomp : ((Scheme.Modules.pullback f).obj F).presheaf.map
        ((Opens.map f.base).map (homOfLE h)).op ≫
      ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom hV'.symm).op =
      ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom hV.symm).op := by
    rw [← Functor.map_comp]
    congr 1
  rw [pullbackSectionsAt, pullbackSectionsAt]
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg (fun u => ((Scheme.Modules.pullback f).obj F).presheaf.map
        (eqToHom hV'.symm).op u) key).trans
      (((ConcreteCategory.comp_apply _ _ _).symm.trans
        (ConcreteCategory.congr_hom hcomp _)).trans
          (ConcreteCategory.comp_apply _ _ _).symm))

end AlgebraicGeometry

namespace Stacks.Algebraization

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

section

variable [IsClosedImmersion i]

/-- Every infinitesimal neighbourhood of a closed immersion has the image of the immersion. -/
public theorem range_nthInfinitesimalNeighbourhoodι (n : ℕ) :
    Set.range (nthInfinitesimalNeighbourhoodι i n).base = Set.range i.base := by
  have hclosed : IsClosed (Set.range i.liftCoborder.base) :=
    (IsClosedImmersion.isClosedEmbedding i.liftCoborder).isClosed_range
  have hsupp : ((i.liftCoborder.ker ^ (n + 1)).support : Set i.coborderRange.toScheme) =
      Set.range i.liftCoborder.base := by
    rw [Scheme.IdealSheafData.support_pow_succ, Scheme.Hom.support_ker]
    exact hclosed.closure_eq
  have h₁ : Set.range ((i.liftCoborder.ker ^ (n + 1)).subschemeι).base =
      Set.range i.liftCoborder.base :=
    (Scheme.IdealSheafData.range_subschemeι _).trans hsupp
  have h₂ : Set.range (nthInfinitesimalNeighbourhoodι i n).base =
      i.coborderRange.ι.base '' Set.range ((i.liftCoborder.ker ^ (n + 1)).subschemeι).base := by
    change Set.range ((i.liftCoborder.ker ^ (n + 1)).subschemeι ≫ i.coborderRange.ι).base = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have h₃ : Set.range (i.liftCoborder ≫ i.coborderRange.ι).base =
      i.coborderRange.ι.base '' Set.range i.liftCoborder.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact h₂.trans ((congrArg (fun S => i.coborderRange.ι.base '' S) h₁).trans
    (h₃.symm.trans (congrArg (fun g : Z ⟶ X => Set.range g.base) i.liftCoborder_ι)))

/-- An open containing a closed subscheme contains all its infinitesimal neighbourhoods. -/
public theorem nthInfinitesimalNeighbourhoodι_preimage_eq_top {V : X.Opens}
    (hV : Set.range i.base ⊆ V) (n : ℕ) :
    (nthInfinitesimalNeighbourhoodι i n) ⁻¹ᵁ V = ⊤ :=
  le_antisymm le_top fun x _ =>
    hV ((range_nthInfinitesimalNeighbourhoodι i n).le (Set.mem_range_self x))

/-- Restriction of a section over an open neighbourhood of a closed subscheme to the `n`-th
infinitesimal neighbourhood. -/
public def neighbourhoodSections (F : X.Modules) {V : X.Opens}
    (hV : Set.range i.base ⊆ V) (n : ℕ) :
    Γ(F, V) ⟶ Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F, ⊤) :=
  pullbackSectionsAt (nthInfinitesimalNeighbourhoodι i n) F
    (nthInfinitesimalNeighbourhoodι_preimage_eq_top i hV n)

/-- The colimit of the sections over the open neighbourhoods of a closed subscheme is the inverse
limit of the sections on its infinitesimal neighbourhoods: every compatible family comes from a
neighbourhood, and two sections inducing the same family agree on a smaller neighbourhood. -/
public def IsNeighbourhoodSectionsComplete (F : X.Modules) : Prop :=
  (∀ s : ∀ n : ℕ,
        Γ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).obj F, ⊤),
      (∀ (n m : ℕ) (h : n ≤ m),
          pullbackSectionsMap F (nthInfinitesimalNeighbourhoodTransition i h) (s m) = s n) →
      ∃ (V : X.Opens) (hV : Set.range i.base ⊆ V) (t : Γ(F, V)),
        ∀ n : ℕ, neighbourhoodSections i F hV n t = s n) ∧
  (∀ (V W : X.Opens) (hV : Set.range i.base ⊆ V) (hW : Set.range i.base ⊆ W)
      (t : Γ(F, V)) (u : Γ(F, W)),
      (∀ n : ℕ, neighbourhoodSections i F hV n t = neighbourhoodSections i F hW n u) →
      ∃ (V' : X.Opens) (_ : Set.range i.base ⊆ V') (h₁ : V' ≤ V) (h₂ : V' ≤ W),
        F.presheaf.map (homOfLE h₁).op t = F.presheaf.map (homOfLE h₂).op u)

/-- Neighbourhood section completeness only depends on the isomorphism class of the module. -/
public theorem isNeighbourhoodSectionsComplete_of_iso {F G : X.Modules} (e : F ≅ G)
    (h : IsNeighbourhoodSectionsComplete i F) : IsNeighbourhoodSectionsComplete i G := by
  obtain ⟨hsurj, hinj⟩ := h
  refine ⟨fun s hs => ?_, fun V W hV hW t u htu => ?_⟩
  · obtain ⟨V, hV, t, ht⟩ := hsurj
      (fun n => ((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).map e.inv).app ⊤
        (s n))
      (fun n m hnm =>
        (pullbackSectionsMap_natural e.inv
            (nthInfinitesimalNeighbourhoodTransition i hnm) (s m)).trans
          (congrArg (fun u => ((Scheme.Modules.pullback
              (nthInfinitesimalNeighbourhoodι i n)).map e.inv).app ⊤ u) (hs n m hnm)))
    refine ⟨V, hV, e.hom.app V t, fun n => ?_⟩
    refine (pullbackSectionsAt_natural _ e.hom _ t).trans ?_
    refine (congrArg (fun u => ((Scheme.Modules.pullback
      (nthInfinitesimalNeighbourhoodι i n)).map e.hom).app ⊤ u) (ht n)).trans ?_
    exact congrArg (fun χ => Scheme.Modules.Hom.app χ ⊤ (s n))
      (((Scheme.Modules.pullback (nthInfinitesimalNeighbourhoodι i n)).mapIso e).inv_hom_id)
  · obtain ⟨V', hV', h₁, h₂, hres⟩ := hinj V W hV hW (e.inv.app V t) (e.inv.app W u) (fun n => by
      refine (pullbackSectionsAt_natural _ e.inv _ t).trans ?_
      refine Eq.trans ?_ (pullbackSectionsAt_natural _ e.inv _ u).symm
      exact congrArg (fun v => ((Scheme.Modules.pullback
        (nthInfinitesimalNeighbourhoodι i n)).map e.inv).app ⊤ v) (htu n))
    refine ⟨V', hV', h₁, h₂, ?_⟩
    have key {U : X.Opens} (g : V' ⟶ U) (v : Γ(G, U)) :
        e.hom.app V' (F.presheaf.map g.op (e.inv.app U v)) = G.presheaf.map g.op v :=
      (NatTrans.naturality_apply e.hom.mapPresheaf g.op (e.inv.app U v)).trans
        (congrArg (fun w => G.presheaf.map g.op w)
          (congrArg (fun χ => Scheme.Modules.Hom.app χ U v) e.inv_hom_id))
    exact (key _ t).symm.trans
      ((congrArg (fun v => Scheme.Modules.Hom.app e.hom V' v) hres).trans (key _ u))

end

/-- **Condition (1) implies condition (2).** Let `i : Y ⟶ X` be a closed immersion into a
Noetherian quasi-affine scheme such that the colimit of the sections of `𝒪_X` over the open
neighbourhoods of `Y` is the limit of its sections on the infinitesimal neighbourhoods. Then `X`
carries an ample invertible module `L` for which the same holds for every tensor power `L^{⊗ m}`
with `m` large enough. -/
@[stacks 0EK2 "(1) implies (2)"]
public theorem quasiAffine_neighbourhoodSectionsComplete_implies_amplePower
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (hX : Scheme.IsQuasiAffine X)
    (h : IsNeighbourhoodSectionsComplete i (SheafOfModules.unit X.ringCatSheaf)) :
    ∃ (L : X.Modules)
      (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L),
      letI := hL
      AlgebraicGeometry.Scheme.Modules.IsAmple X L ∧
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
          IsNeighbourhoodSectionsComplete i
            (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
              (structureSheafRing X.toRingedSpace).property L (m : ℤ)) := by
  have := hX
  have h1 : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property (SheafOfModules.unit X.ringCatSheaf) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_unit X
  have h2 : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property
      (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property)) :=
    AlgebraicGeometry.Scheme.Modules.isInvertible_unit X
  refine ⟨SheafOfModules.unit X.ringCatSheaf, h1, ?_, 0, fun m _ => ?_⟩
  · exact AlgebraicGeometry.Scheme.Modules.isAmple_unit_of_isQuasiAffine X
  · exact isNeighbourhoodSectionsComplete_of_iso i
      (Stacks.SheafOfModules.Invertible.tensorPowerUnitIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property m).symm h

end Stacks.Algebraization

end
