module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.IdealPowerQuotientTower
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedTowerLift

/-!
# The tower of algebraizations is a coherent adic system along the second ideal

Let `X` be a Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves and let `(F_n)`
be an object of `Coh(X, ℐ)`. Granted hypothesis (1) of [Stacks, Tag 088A] at every level,
`Stacks.Coherent.exists_lifted_quotient_tower` produces a tower `(G_e)` of coherent
`𝒪_X`-modules, the term `e` annihilated by `𝒦 ᵉ⁺¹`, whose termwise `ℐ`-completion is identified
naturally in `e` with the tower of reductions `(F_n / 𝒦 ᵉ⁺¹ F_n)`. It is a bare functor
`ℕᵒᵖ ⥤ Coh(𝒪_X)`; the rest of the proof of Tag 088A applies Tag 0889 along `𝒦` to it, and for
that it has to be an object of `Coh(X, 𝒦)`.

This file supplies the missing clause: the transition `G_{e+1} ⟶ G_e` descends to an
isomorphism `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ≅ G_e`. The descent is produced after completion, where
the three identifications

* completion commutes with reduction modulo `𝒦 ᵉ⁺¹`,
* the given identification of the completed tower with the tower of reductions, and
* the collapse `(F_n / 𝒦 ᵉ⁺² F_n) / 𝒦 ᵉ⁺¹ (…) ≅ F_n / 𝒦 ᵉ⁺¹ F_n`

exhibit the completion of the descent as an isomorphism; completion reflects isomorphisms
between `𝒦 ᵉ⁺¹`-annihilated coherent modules
(`Stacks.Coherent.isIso_of_isIso_completion_map_of_power_annihilated`), so the descent itself is
one.

## Main definitions

* `Stacks.Coherent.coherentIdealPowerQuotientFunctor` — reduction modulo `𝒦 ʳ` as an endofunctor
  of `Coh(𝒪_X)`, with its projection
  `Stacks.Coherent.coherentIdealPowerQuotientProjection` from the identity.
* `Stacks.Coherent.idealPowerQuotientAdicCompletionIso` — the `𝒦 ʳ`-reduction of the
  `ℐ`-completion of `M` is the `ℐ`-completion of `M / 𝒦 ʳ M`, as an isomorphism in
  `Coh(X, ℐ)`.
* `Stacks.Coherent.idealPowerQuotientAdicCollapseIso` — iterated reduction of a coherent adic
  system collapses onto the smaller power.

## Main results

* `Stacks.Coherent.completion_quotientDesc_eq` — the completion of the descent of a morphism
  through a reduction projection, computed from the three identifications above.
* `Stacks.Coherent.isCoherentAdicSystem_liftedQuotientTower` — **the tower of algebraizations is
  an object of `Coh(X, 𝒦)`.**

## Implementation notes

Both comparisons are the adic-system forms of comparisons the library already has for the
underlying inverse systems, `Stacks.Coherent.completionIdealPowerQuotientSystemIso` and
`Stacks.Coherent.idealPowerQuotientSystemCollapseIso`; promoting them to the full subcategory
`Coh(X, ℐ)` is `CategoryTheory.ObjectProperty.isoMk`, and all the content of their naturality is
already discharged there.

The computation of the completion of a descent is isolated as
`Stacks.Coherent.map_desc_eq_of_projection`, a statement about an arbitrary functor and an
arbitrary pointwise-epimorphic projection onto an endofunctor; this keeps the diagram chase away
from the two abelian structures involved.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-! ### Reduction modulo a power of `𝒦` on coherent modules -/

/-- **Reduction modulo `𝒦 ʳ` as an endofunctor of `Coh(𝒪_X)`.** -/
public def coherentIdealPowerQuotientFunctor (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf where
  obj M := coherentIdealPowerQuotient K M r
  map f := ObjectProperty.homMk (idealPowerQuotientMap K K r r le_rfl f.hom)
  map_id M := ObjectProperty.hom_ext _ (idealPowerQuotientMap_id K r M.obj)
  map_comp f g := ObjectProperty.hom_ext _ (idealPowerQuotientMap_comp K r f.hom g.hom)

/-- **The projection of a coherent module onto its `𝒦 ʳ`-reduction.** -/
public def coherentIdealPowerQuotientProjection (r : ℕ) :
    𝟭 (AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) ⟶
      coherentIdealPowerQuotientFunctor K r where
  app M := ObjectProperty.homMk
    (cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι)
  naturality _ _ f :=
    ObjectProperty.hom_ext _ (idealPowerQuotientMap_π K K r r le_rfl f.hom).symm

/-! ### Completion commutes with reduction, as an isomorphism of coherent adic systems -/

/-- **Completion along `ℐ` commutes with reduction modulo `𝒦 ʳ`**, as an isomorphism in
`Coh(X, ℐ)`: the `𝒦 ʳ`-reduction of `M ^∧_ℐ` is the `ℐ`-completion of `M / 𝒦 ʳ M`.

This is `Stacks.Coherent.completionIdealPowerQuotientSystemIso` promoted to the full
subcategory. -/
public def idealPowerQuotientAdicCompletionIso
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (r : ℕ) :
    (idealPowerQuotientAdicFunctor I K r).obj ((completionFunctor X I).obj M) ≅
      (completionFunctor X I).obj ((coherentIdealPowerQuotientFunctor K r).obj M) :=
  (ObjectProperty.isoMk (IsCoherentAdicSystem I)
    (completionIdealPowerQuotientSystemIso I K M r)).symm

/-- **The comparison is normalized by the projections.** -/
public theorem idealPowerQuotientAdicProjection_comp_adicCompletionIso
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (r : ℕ) :
    (idealPowerQuotientAdicProjection I K r).app ((completionFunctor X I).obj M) ≫
        (idealPowerQuotientAdicCompletionIso I K M r).hom =
      (completionFunctor X I).map ((coherentIdealPowerQuotientProjection K r).app M) := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  refine (Stacks.Algebraization.epi_completionProjection X I M n.unop).left_cancellation
    _ _ ?_
  have hterm := completionIdealPowerQuotientTermIso_projection I K M r n.unop
  have hcancel : completionProjection X I (coherentIdealPowerQuotient K M r) n.unop ≫
      ((completionIdealPowerQuotientTermIso I K M r n.unop).hom ≫
        (completionIdealPowerQuotientTermIso I K M r n.unop).inv) =
      completionProjection X I (coherentIdealPowerQuotient K M r) n.unop :=
    (congrArg (fun z => completionProjection X I
      (coherentIdealPowerQuotient K M r) n.unop ≫ z)
        (completionIdealPowerQuotientTermIso I K M r n.unop).hom_inv_id).trans
      (Category.comp_id _)
  have hleft : completionProjection X I M n.unop ≫
      (((idealPowerQuotientAdicProjection I K r).app
            ((completionFunctor X I).obj M)).hom.app n ≫
        (idealPowerQuotientAdicCompletionIso I K M r).hom.hom.app n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple K r M.obj).ι ≫
        completionProjection X I (coherentIdealPowerQuotient K M r) n.unop := by
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _).symm ?_
    refine Eq.trans (congrArg (fun z => z ≫
      (idealPowerQuotientAdicCompletionIso I K M r).hom.hom.app n) hterm.symm) ?_
    refine Eq.trans (Category.assoc (obj := X.Modules) _ _ _) ?_
    refine Eq.trans (congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫ z)
        (Category.assoc (obj := X.Modules) _ _ _)) ?_
    exact congrArg (fun z => cokernel.π (C := X.Modules)
      (idealPowerMultiple K r M.obj).ι ≫ z) hcancel
  refine hleft.trans ?_
  exact (completionFunctor_map_quotient X I
    ((coherentIdealPowerQuotientProjection K r).app M) n.unop).symm

/-- **The projection onto a reduction is an epimorphism of coherent adic systems.** -/
public theorem epi_idealPowerQuotientAdicProjection (r : ℕ) (F : CoherentAdicSystems I) :
    Epi ((idealPowerQuotientAdicProjection I K r).app F) := by
  have : ∀ n : ℕᵒᵖ, Epi (((ObjectProperty.ι (IsCoherentAdicSystem I)).map
      ((idealPowerQuotientAdicProjection I K r).app F)).app n) := fun n =>
    epi_cokernel_π_submodule_ι (idealPowerMultiple K r (F.obj.obj n))
  exact (ObjectProperty.ι (IsCoherentAdicSystem I)).epi_of_epi_map
    (NatTrans.epi_of_epi_app _)

/-! ### Iterated reduction of a coherent adic system -/

/-- **Iterated reduction of a coherent adic system collapses onto the smaller power.** For
`r ≤ s`, the `𝒦 ʳ`-reduction of the `𝒦 ˢ`-reduction of a coherent adic system is its
`𝒦 ʳ`-reduction.

This is `Stacks.Coherent.idealPowerQuotientSystemCollapseIso` promoted to the full
subcategory. -/
public def idealPowerQuotientAdicCollapseIso {r s : ℕ} (hrs : r ≤ s)
    (F : CoherentAdicSystems I) :
    (idealPowerQuotientAdicFunctor I K r).obj
        ((idealPowerQuotientAdicFunctor I K s).obj F) ≅
      (idealPowerQuotientAdicFunctor I K r).obj F :=
  ObjectProperty.isoMk (IsCoherentAdicSystem I)
    (idealPowerQuotientSystemCollapseIso K hrs F.obj
      (fun n => F.property.isQuasicoherent n.unop))

/-- **The collapse is normalized by the projection, and identifies with the transition of the
tower of reductions.** -/
public theorem idealPowerQuotientAdicProjection_comp_collapseIso {r s : ℕ} (hrs : r ≤ s)
    (F : CoherentAdicSystems I) :
    (idealPowerQuotientAdicProjection I K r).app
        ((idealPowerQuotientAdicFunctor I K s).obj F) ≫
        (idealPowerQuotientAdicCollapseIso I K hrs F).hom =
      (idealPowerQuotientAdicDrop I K hrs).app F := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  have := F.property.isQuasicoherent n.unop
  refine (epi_cokernel_π_submodule_ι
    (idealPowerMultiple K s (F.obj.obj n))).left_cancellation _ _ ?_
  have hleft : cokernel.π (C := X.Modules) (idealPowerMultiple K s (F.obj.obj n)).ι ≫
      (((idealPowerQuotientAdicProjection I K r).app
            ((idealPowerQuotientAdicFunctor I K s).obj F)).hom.app n ≫
        (idealPowerQuotientAdicCollapseIso I K hrs F).hom.hom.app n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple K r (F.obj.obj n)).ι :=
    (Category.assoc (obj := X.Modules) _ _ _).symm.trans
      (doubleIdealPowerQuotientProjection_comp_idealPowerQuotientCollapseIso K hrs
        (F.obj.obj n))
  exact hleft.trans (idealPowerQuotientDrop'_π K hrs (F.obj.obj n)).symm

/-! ### The completion of a descent -/

/-- **The completion of a descent through a reduction projection.** Let `A` be a functor, let
`T` be an endofunctor of its target equipped with a transformation `p : 𝟭 ⟶ T`, let `d : Q ⟶ N`
be a morphism factoring a given `f : M ⟶ N` through a morphism `q : M ⟶ Q` whose image under `A`
is an epimorphism, and suppose `T (A M)` is identified with `A Q` compatibly with the
projections. Then `A d` is computed from `f` and the identifications.

This is the shape of the computation that identifies the completion of
`G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1} ⟶ G_e` with an isomorphism. -/
public theorem map_desc_eq_of_projection
    {C D : Type*} [Category C] [Category D] (A : C ⥤ D) (T : D ⥤ D)
    (p : 𝟭 D ⟶ T) {M Q N : C} {U V : D}
    (q : M ⟶ Q) (d : Q ⟶ N) (f : M ⟶ N) (hqd : q ≫ d = f)
    (c : T.obj (A.obj M) ≅ A.obj Q) (hp : p.app (A.obj M) ≫ c.hom = A.map q)
    (u : A.obj M ≅ U) (v : A.obj N ≅ V) (w : T.obj U ≅ V) (τ : U ⟶ V)
    (hτ : p.app U ≫ w.hom = τ) (hf : A.map f ≫ v.hom = u.hom ≫ τ)
    [Epi (A.map q)] : A.map d = c.inv ≫ T.map u.hom ≫ w.hom ≫ v.inv := by
  apply (cancel_epi (A.map q)).mp
  rw [← A.map_comp, hqd, ← hp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← p.naturality]
  dsimp only [Functor.id_map]
  rw [Category.assoc, reassoc_of% hτ]
  apply (cancel_mono v.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hf

/-- **The completion of the descent of a transition through a reduction projection.** With
`M`, `N` coherent modules, `N` annihilated by `𝒦 ᵉ⁺¹`, identifications of their `ℐ`-completions
with two consecutive reductions of a coherent adic system `(F_n)`, and a morphism `f : M ⟶ N`
whose completion is the transition between those reductions, the completion of the descent of
`f` through the projection `M ⟶ M / 𝒦 ᵉ⁺¹ M` is the composite of three isomorphisms. -/
public theorem completion_quotientDesc_eq (F : CoherentAdicSystems I) (e : ℕ)
    (M N : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (f : M ⟶ N)
    (hN : idealPowerMultiple K (e + 1) N.obj = ⊥)
    (cM : (completionFunctor X I).obj M ≅
      (idealPowerQuotientAdicFunctor I K (e + 1 + 1)).obj F)
    (cN : (completionFunctor X I).obj N ≅ (idealPowerQuotientAdicFunctor I K (e + 1)).obj F)
    (hf : (completionFunctor X I).map f ≫ cN.hom =
      cM.hom ≫ (idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1))).app F) :
    (completionFunctor X I).map
        (ObjectProperty.homMk (idealPowerQuotientDesc K (e + 1) f.hom hN) :
          (coherentIdealPowerQuotientFunctor K (e + 1)).obj M ⟶ N) =
      ((idealPowerQuotientAdicCompletionIso I K M (e + 1)).symm ≪≫
        (idealPowerQuotientAdicFunctor I K (e + 1)).mapIso cM ≪≫
        idealPowerQuotientAdicCollapseIso I K (Nat.le_succ (e + 1)) F ≪≫ cN.symm).hom := by
  have hepi : Epi ((completionFunctor X I).map
      ((coherentIdealPowerQuotientProjection K (e + 1)).app M)) := by
    have := epi_idealPowerQuotientAdicProjection I K (e + 1) ((completionFunctor X I).obj M)
    have h := epi_comp
      ((idealPowerQuotientAdicProjection I K (e + 1)).app ((completionFunctor X I).obj M))
      (idealPowerQuotientAdicCompletionIso I K M (e + 1)).hom
    rwa [idealPowerQuotientAdicProjection_comp_adicCompletionIso] at h
  exact map_desc_eq_of_projection (completionFunctor X I)
    (idealPowerQuotientAdicFunctor I K (e + 1))
    (idealPowerQuotientAdicProjection I K (e + 1))
    ((coherentIdealPowerQuotientProjection K (e + 1)).app M)
    (ObjectProperty.homMk (idealPowerQuotientDesc K (e + 1) f.hom hN)) f
    (ObjectProperty.hom_ext _ (idealPowerQuotientDesc_π K (e + 1) f.hom hN))
    (idealPowerQuotientAdicCompletionIso I K M (e + 1))
    (idealPowerQuotientAdicProjection_comp_adicCompletionIso I K M (e + 1)) cM cN
    (idealPowerQuotientAdicCollapseIso I K (Nat.le_succ (e + 1)) F)
    ((idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1))).app F)
    (idealPowerQuotientAdicProjection_comp_collapseIso I K (Nat.le_succ (e + 1)) F) hf

/-! ### The tower of algebraizations as an object of `Coh(X, 𝒦)` -/

/-- **Tag 088A: the tower of algebraizations is a coherent adic system along `𝒦`.** Let `X` be
Noetherian, let `ℐ, 𝒦` be quasi-coherent ideal sheaves satisfying hypothesis (1) of
[Stacks, Tag 088A] at every level, and let `(G_e)` be a tower of coherent `𝒪_X`-modules, the
term `e` annihilated by `𝒦 ᵉ⁺¹`, whose termwise `ℐ`-completion is identified naturally with the
tower of `𝒦 ᵉ⁺¹`-reductions of an object `(F_n)` of `Coh(X, ℐ)`. Then the underlying inverse
system of `(G_e)` is an object of `Coh(X, 𝒦)`.

Only the quotient clause needs proof. The transition `G_{e+1} ⟶ G_e` descends through the
projection onto `G_{e+1} / 𝒦 ᵉ⁺¹ G_{e+1}`, and `Stacks.Coherent.completion_quotientDesc_eq`
identifies the completion of that descent with the composite of
`Stacks.Coherent.idealPowerQuotientAdicCompletionIso`, the given identification and
`Stacks.Coherent.idealPowerQuotientAdicCollapseIso`, hence with an isomorphism. Both modules are
annihilated by `𝒦 ᵉ⁺¹`, so completion reflects the isomorphism by
`Stacks.Coherent.isIso_of_isIso_completion_map_of_power_annihilated`. -/
@[stacks 088A "proof step 4, adic form: the tower of algebraizations lies in Coh(X, 𝒦)"]
public theorem isCoherentAdicSystem_liftedQuotientTower [IsNoetherian X]
    (F : CoherentAdicSystems I) (h : IsCompletionEquivalenceOnPowerThickenings I K)
    (G : ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hG : ∀ e : ℕ, idealPowerMultiple K (e + 1) (G.obj (op e)).obj = ⊥)
    (c : G ⋙ completionFunctor X I ≅
      idealPowerQuotientAdicTower I K ⋙ (evaluation _ _).obj F) :
    IsCoherentAdicSystem K (G ⋙ ObjectProperty.ι _) := by
  refine ⟨fun e => (G.obj (op e)).property, hG, fun e => ?_⟩
  have : (G.obj (op (e + 1))).obj.IsCoherent := (G.obj (op (e + 1))).property
  have : (G.obj (op (e + 1))).obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  set transition := G.map (homOfLE (Nat.le_succ e)).op with htransition
  set descended : (coherentIdealPowerQuotientFunctor K (e + 1)).obj (G.obj (op (e + 1))) ⟶
      G.obj (op e) :=
    ObjectProperty.homMk (idealPowerQuotientDesc K (e + 1) transition.hom (hG e))
    with hdescended
  have hf : (completionFunctor X I).map transition ≫ (c.app (op e)).hom =
      (c.app (op (e + 1))).hom ≫
        (idealPowerQuotientAdicDrop I K (Nat.le_succ (e + 1))).app F := by
    have hnat := c.hom.naturality (homOfLE (Nat.le_succ e)).op
    refine Eq.trans hnat ?_
    exact congrArg (fun φ : idealPowerQuotientAdicFunctor I K (e + 1 + 1) ⟶
        idealPowerQuotientAdicFunctor I K (e + 1) =>
      (c.app (op (e + 1))).hom ≫ φ.app F) (idealPowerQuotientAdicTower_map_succ I K e)
  have himage := completion_quotientDesc_eq I K F e (G.obj (op (e + 1))) (G.obj (op e))
    transition (hG e) (c.app (op (e + 1))) (c.app (op e)) hf
  have : IsIso ((completionFunctor X I).map descended) := by
    rw [hdescended, himage]
    infer_instance
  have : IsIso descended :=
    isIso_of_isIso_completion_map_of_power_annihilated I K e (h e)
      (idealPowerMultiple_idealPowerQuotient_eq_bot K (e + 1) (G.obj (op (e + 1))).obj)
      (hG e) descended
  refine ⟨(ObjectProperty.ι _).mapIso (asIso descended), ?_⟩
  exact idealPowerQuotientDesc_π K (e + 1) transition.hom (hG e)

end Stacks.Coherent

end
