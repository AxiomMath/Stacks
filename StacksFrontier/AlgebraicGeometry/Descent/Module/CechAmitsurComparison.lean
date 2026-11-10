module

public import Mathlib.CategoryTheory.Monad.Limits
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechComplexAndAmitsur

/-!
# The Čech complex of a one-member covering is the Amitsur complex

Let `h : V ⟶ T` be a morphism in a category with finite limits and let `ℱ` be an additive
presheaf. For `R = Γ(T, 𝒪)`, `A = Γ(V, 𝒪)` and `M = Γ(T, ℱ)`, the Čech complex `Č^•({V → T}, ℱ)`
is identified with the complex `s((A/R)_• ⊗_R M)` of Stacks Section 023F, termwise and
differentialwise, given that the degreewise comparison maps are isomorphisms.

The identification is an isomorphism of cosimplicial objects. Degree `p` of the Čech cosimplicial
object of `{V → T}` is `ℱ(V ×_T ⋯ ×_T V)`, degree `p` of `(A/R)_• ⊗_R M` is
`(A ⊗_R ⋯ ⊗_R A) ⊗_R M`, and the `(p + 1)`-fold tensor power is the wide pushout of `p + 1` copies
of `A` under `R`. The comparison map in degree `p` is the map out of that wide pushout determined
by the `p + 1` projections of `V ×_T ⋯ ×_T V`.

## Main definitions

* `Stacks.CechSite.powerSections` is the cosimplicial object `⦋p⦌ ↦ H(Y^{p+1})` of the values
  of a presheaf on the powers of an object.
* `Stacks.CechSite.singletonCechCosimplicialIso` identifies the Čech cosimplicial object of
  the one-member family `{V → T}` with `Stacks.CechSite.powerSections`, by discarding the
  one-fold product over the singleton index type.
* `Stacks.CechSite.conerveSectionsMap` is the degreewise comparison map from the Čech conerve
  of `H(⊤) ⟶ H(Y)` to `H(Y^{p+1})`, and `Stacks.CechSite.conerveSectionsComparison` is the
  morphism of cosimplicial objects it assembles into.
* `Stacks.CechSite.conerveSectionsIso` upgrades it to an isomorphism of cosimplicial objects
  when it is a degreewise isomorphism.
* `Stacks.CechSite.sectionsTerminalArrowIsoOfAdjunction` and
  `Stacks.CechSite.isColimitPowerSectionsCoconeOfAdjunction`: for an adjunction whose right
  adjoint is fully faithful and limit-preserving, the sections of the terminal arrow at an object
  in its image are the structure arrow of that object, and the sections of its powers are the
  wide pushout of its sections.
* `Stacks.Descent.cechCosimplicialObjectIsoAmitsurOfPowerSections` is the variant of the
  identification below whose coefficient hypothesis is asked only at the fibre powers.
* `Stacks.Descent.amitsurCoefficients` is the coefficient functor `S ↦ S ⊗_R M` of the Amitsur
  complex.
* `Stacks.Descent.cechCosimplicialObjectIsoAmitsur` is the resulting identification of the
  Čech cosimplicial object of `{V → T}` with `(A/R)_• ⊗_R M`.
* `Stacks.Descent.cechComplexSingletonIsoAmitsur` is the induced isomorphism of complexes
  `Č^•({V → T}, ℱ) ≅ s((A/R)_• ⊗_R M)`, termwise *and* differentialwise.

## Main results

* `Stacks.CechSite.conerveSectionsMap_naturality`: the degreewise comparison maps commute with
  the cosimplicial structure maps.
* `Stacks.Descent.isZero_cechCohomology_singleton_succ_of_conerveSectionsIso`:
  `Ȟ^p({V → T}, ℱ) = 0` for `p ≥ 1`, when `A` is faithfully flat over `R`.
* `Stacks.Descent.isZero_cechCohomology_singleton_succ_of_adjunction_of_powerSections`: the
  same under an adjunction, so that no hypothesis about the fibre powers is carried.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 023F](https://stacks.math.columbia.edu/tag/023F)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite

universe w v v' u u' uR uA uM

namespace Stacks.CechSite

/-! ### The sections of the powers of an object -/

section Conerve

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] (Y : D)
  {A : Type u'} [Category.{v'} A] (H : Dᵒᵖ ⥤ A)

/-- The arrow `H(⊤) ⟶ H(Y)` obtained by applying a presheaf to the morphism from an object to
the terminal object. -/
noncomputable abbrev sectionsTerminalArrow : Arrow A :=
  Arrow.mk (H.map (terminal.from Y).op)

/-- The cosimplicial object `⦋p⦌ ↦ H(Y^{p+1})` of the values of a presheaf on the powers of an
object. It is the Čech cosimplicial object of the one-member family `{Y → ⊤}`. -/
noncomputable abbrev powerSections : CosimplicialObject A :=
  (cechNerveTerminalFrom Y).rightOp ⋙ H

/-- The structural map `H(⊤) ⟶ H(Y^{p+1})`, the head of the wide pushout cocone. -/
noncomputable def powerSectionsHead (n : SimplexCategory) :
    (sectionsTerminalArrow Y H).left ⟶ (powerSections Y H).obj n :=
  H.map (terminal.from ((cechNerveTerminalFrom Y).obj (op n))).op

/-- The `a`-th projection `H(Y) ⟶ H(Y^{p+1})`, a leg of the wide pushout cocone. -/
noncomputable def powerSectionsIncl (n : SimplexCategory) (a : Fin (n.len + 1)) :
    (sectionsTerminalArrow Y H).right ⟶ (powerSections Y H).obj n :=
  H.map (Pi.π (fun _ : Fin (n.len + 1) => Y) a).op

/-- A presheaf turns a factorisation `f ≫ g = k` into `K(g) ≫ K(f) = K(k)`. -/
private lemma map_op_comp_eq {E : Type*} [Category E] {B : Type*} [Category B] (K : Eᵒᵖ ⥤ B)
    {X Y Z : E} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    K.map g.op ≫ K.map f.op = K.map k.op := by
  rw [← K.map_comp, ← op_comp, hk]

/-- The legs of the cocone all restrict to the head along the arrow `H(⊤) ⟶ H(Y)`: the
projections of a power compose with the map to the terminal object to the same map. -/
lemma arrow_comp_powerSectionsIncl (n : SimplexCategory) (a : Fin (n.len + 1)) :
    (sectionsTerminalArrow Y H).hom ≫ powerSectionsIncl Y H n a = powerSectionsHead Y H n :=
  map_op_comp_eq H _ _ _ (terminal.comp_from _)

/-- A cosimplicial structure map of `Stacks.CechSite.powerSections` carries the `a`-th
projection to the projection at the reindexed slot. -/
lemma powerSectionsIncl_comp_map {n m : SimplexCategory} (g : n ⟶ m) (a : Fin (n.len + 1)) :
    powerSectionsIncl Y H n a ≫ (powerSections Y H).map g =
      powerSectionsIncl Y H m (g.toOrderHom a) := by
  exact map_op_comp_eq H _ _ _ (Pi.lift_comp_π _ _)

/-- A cosimplicial structure map of `Stacks.CechSite.powerSections` fixes the head. -/
lemma powerSectionsHead_comp_map {n m : SimplexCategory} (g : n ⟶ m) :
    powerSectionsHead Y H n ≫ (powerSections Y H).map g = powerSectionsHead Y H m :=
  map_op_comp_eq H _ _ _ (terminal.comp_from _)

/-- The cocone of the `p + 1` projections of `Y^{p+1}`, under the sections of the terminal
object. -/
noncomputable def powerSectionsCocone (n : SimplexCategory) :
    Cocone (WidePushoutShape.wideSpan (sectionsTerminalArrow Y H).left
      (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).right)
      (fun _ => (sectionsTerminalArrow Y H).hom)) :=
  WidePushoutShape.mkCocone (powerSectionsHead Y H n) (powerSectionsIncl Y H n)
    (arrow_comp_powerSectionsIncl Y H n)

variable [∀ n : ℕ, HasWidePushout (sectionsTerminalArrow Y H).left
  (fun _ : Fin (n + 1) => (sectionsTerminalArrow Y H).right)
  (fun _ => (sectionsTerminalArrow Y H).hom)]

/-- The degreewise comparison map from the Čech conerve of `H(⊤) ⟶ H(Y)` to `H(Y^{p+1})`:
the map out of the wide pushout determined by the `p + 1` projections of the power. -/
noncomputable def conerveSectionsMap (n : SimplexCategory) :
    (sectionsTerminalArrow Y H).cechConerve.obj n ⟶ (powerSections Y H).obj n :=
  WidePushout.desc (powerSectionsHead Y H n) (powerSectionsIncl Y H n)
    (arrow_comp_powerSectionsIncl Y H n)

/-- The comparison map is an isomorphism when the cocone of the projections of the power is a
wide pushout. -/
lemma isIso_conerveSectionsMap (n : SimplexCategory)
    (hc : IsColimit (powerSectionsCocone Y H n)) :
    IsIso (conerveSectionsMap Y H n) := by
  have hmap : conerveSectionsMap Y H n =
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc).hom := rfl
  exact hmap ▸ (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc).isIso_hom

/-- The comparison map restricts along the `a`-th coprojection of the pushout to the `a`-th
projection of the power. -/
lemma ι_comp_conerveSectionsMap (n : SimplexCategory) (a : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) a ≫
        conerveSectionsMap Y H n = powerSectionsIncl Y H n a :=
  WidePushout.ι_desc (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) _ _ _ a

/-- The comparison map restricts along the head of the pushout to the structural map. -/
lemma head_comp_conerveSectionsMap (n : SimplexCategory) :
    WidePushout.head (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) ≫
        conerveSectionsMap Y H n = powerSectionsHead Y H n :=
  WidePushout.head_desc (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) _ _ _

/-- A cosimplicial structure map of a Čech conerve carries the `a`-th coprojection to the
coprojection at the reindexed slot. -/
lemma ι_comp_cechConerve_map {n m : SimplexCategory} (g : n ⟶ m) (a : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) a ≫
        (sectionsTerminalArrow Y H).cechConerve.map g =
      WidePushout.ι (fun _ : Fin (m.len + 1) => (sectionsTerminalArrow Y H).hom)
        (g.toOrderHom a) := by
  rw [Arrow.cechConerve_map]
  exact WidePushout.ι_desc (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) _ _ _ a

/-- A cosimplicial structure map of a Čech conerve fixes the head. -/
lemma head_comp_cechConerve_map {n m : SimplexCategory} (g : n ⟶ m) :
    WidePushout.head (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) ≫
        (sectionsTerminalArrow Y H).cechConerve.map g =
      WidePushout.head (fun _ : Fin (m.len + 1) => (sectionsTerminalArrow Y H).hom) := by
  rw [Arrow.cechConerve_map]
  exact WidePushout.head_desc (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow Y H).hom) _ _ _

/-- The degreewise comparison maps commute with the cosimplicial structure maps. -/
lemma conerveSectionsMap_naturality {n m : SimplexCategory} (g : n ⟶ m) :
    (sectionsTerminalArrow Y H).cechConerve.map g ≫ conerveSectionsMap Y H m =
      conerveSectionsMap Y H n ≫ (powerSections Y H).map g := by
  refine WidePushout.hom_ext _ _ _ (fun a => ?_) ?_
  · erw [← Category.assoc, ι_comp_cechConerve_map, ι_comp_conerveSectionsMap, ← Category.assoc,
      ι_comp_conerveSectionsMap, powerSectionsIncl_comp_map]
  · erw [← Category.assoc, head_comp_cechConerve_map, head_comp_conerveSectionsMap,
      ← Category.assoc, head_comp_conerveSectionsMap, powerSectionsHead_comp_map]

/-- The comparison morphism of cosimplicial objects from the Čech conerve of
`H(⊤) ⟶ H(Y)` to the sections of the powers of `Y`. -/
noncomputable def conerveSectionsComparison :
    (sectionsTerminalArrow Y H).cechConerve ⟶ powerSections Y H where
  app n := conerveSectionsMap Y H n
  naturality _ _ g := conerveSectionsMap_naturality Y H g

/-- The Čech conerve of the sections is the sections of the powers, as cosimplicial
objects, when the degreewise comparison map is an isomorphism. -/
noncomputable def conerveSectionsIso
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap Y H n)) :
    (sectionsTerminalArrow Y H).cechConerve ≅ powerSections Y H :=
  haveI : ∀ n, IsIso ((conerveSectionsComparison Y H).app n) := hiso
  haveI : IsIso (conerveSectionsComparison Y H) := NatIso.isIso_of_isIso_app _
  asIso (conerveSectionsComparison Y H)

end Conerve

/-! ### The termwise half from an adjunction -/

section Adjunction

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D]
  {A : Type u'} [Category.{v'} A] {L : D ⥤ Aᵒᵖ} {G : Aᵒᵖ ⥤ D}

/-- The unit of an adjunction whose right adjoint is fully faithful and limit-preserving is
invertible at a power of an object in the image of the right adjoint. -/
lemma isIso_unit_app_pi (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : A) (m : ℕ) :
    IsIso (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a))) :=
  have : Reflective G := { L := L, adj := adj }
  have : HasLimitsOfShape (Discrete (Fin m)) Aᵒᵖ := hasLimitsOfShape_of_reflective G
  Adjunction.isIso_unit_app_of_iso adj (PreservesProduct.iso G fun _ : Fin m => op a).symm

/-- The projections of a power of an object in the image of a fully faithful limit-preserving
right adjoint are jointly monic after applying the left adjoint. -/
lemma hom_ext_map_pi (adj : L ⊣ G) [G.Full] [G.Faithful] [PreservesLimitsOfSize.{0, 0} G]
    {a : A} {m : ℕ} {V : Aᵒᵖ} {ψ χ : V ⟶ L.obj (∏ᶜ fun _ : Fin m => G.obj (op a))}
    (hπ : ∀ i : Fin m, ψ ≫ L.map (Pi.π (fun _ : Fin m => G.obj (op a)) i) =
      χ ≫ L.map (Pi.π (fun _ : Fin m => G.obj (op a)) i)) :
    ψ = χ := by
  have := isIso_unit_app_pi adj a m
  have hcancel : ∀ (θ : V ⟶ L.obj (∏ᶜ fun _ : Fin m => G.obj (op a)))
      (q : (∏ᶜ fun _ : Fin m => G.obj (op a)) ⟶ G.obj (op a)),
      ((G.map θ ≫ inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)))) ≫ q) ≫
        adj.unit.app (G.obj (op a)) = G.map (θ ≫ L.map q) := by
    intro θ q
    calc ((G.map θ ≫ inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)))) ≫ q) ≫
          adj.unit.app (G.obj (op a))
        = (G.map θ ≫ inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)))) ≫
            q ≫ adj.unit.app (G.obj (op a)) := Category.assoc _ _ _
      _ = (G.map θ ≫ inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)))) ≫
            adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)) ≫ G.map (L.map q) :=
          congrArg _ (adj.unit_naturality q).symm
      _ = G.map θ ≫ inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a))) ≫
            adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a)) ≫ G.map (L.map q) :=
          Category.assoc _ _ _
      _ = G.map θ ≫ G.map (L.map q) := congrArg _ (IsIso.inv_hom_id_assoc _ _)
      _ = G.map (θ ≫ L.map q) := (G.map_comp _ _).symm
  exact G.map_injective
    ((cancel_mono (inv (adj.unit.app (∏ᶜ fun _ : Fin m => G.obj (op a))))).1
      (Pi.hom_ext (f := fun _ : Fin m => G.obj (op a)) _ _ fun i =>
        (cancel_mono (adj.unit.app (G.obj (op a)))).1
          ((hcancel ψ _).trans
            ((congrArg (fun t => G.map t) (hπ i)).trans (hcancel χ _).symm))))

/-- Maps out of the sections of a power of an object in the image of the right adjoint are
determined by their restrictions along the projections of the power. -/
lemma hom_ext_powerSectionsIncl (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : A) (n : SimplexCategory) {W : A}
    {φ χ : (powerSections (G.obj (op a)) L.leftOp).obj n ⟶ W}
    (hπ : ∀ i : Fin (n.len + 1), powerSectionsIncl (G.obj (op a)) L.leftOp n i ≫ φ =
      powerSectionsIncl (G.obj (op a)) L.leftOp n i ≫ χ) :
    φ = χ :=
  Quiver.Hom.op_inj (hom_ext_map_pi adj (a := a) (m := n.len + 1) (ψ := φ.op) (χ := χ.op)
    fun i => congrArg Quiver.Hom.op (hπ i))

/-- The sections of the terminal object are the initial object of the target category, under an
adjunction whose right adjoint is fully faithful and preserves limits. -/
noncomputable def sectionsTerminalLeftIsoOfAdjunction (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] {X : A} (hX : IsInitial X) :
    L.leftOp.obj (op (⊤_ D)) ≅ X :=
  (L.mapIso (terminalIsTerminal.uniqueUpToIso
      (IsTerminal.isTerminalObj G _ (terminalOpOfInitial hX))) ≪≫
    asIso (adj.counit.app (op X))).unop.symm

/-- Under an adjunction whose right adjoint is fully faithful and preserves limits, the
sections of the terminal arrow at an object in the image of the right adjoint are the structure
arrow of that object under the initial object. -/
noncomputable def sectionsTerminalArrowIsoOfAdjunction (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] {X : A} (hX : IsInitial X) {a : A} (f : X ⟶ a) :
    sectionsTerminalArrow (G.obj (op a)) L.leftOp ≅ Arrow.mk f :=
  Arrow.isoMk (sectionsTerminalLeftIsoOfAdjunction adj hX)
    (asIso (adj.counit.app (op a))).unop.symm
    ((hX.ofIso (sectionsTerminalLeftIsoOfAdjunction adj hX).symm).hom_ext _ _)

section Desc

variable (adj : L ⊣ G) [G.Full] [G.Faithful] (a : A) (n : SimplexCategory)
  (s : Cocone (WidePushoutShape.wideSpan (sectionsTerminalArrow (G.obj (op a)) L.leftOp).left
    (fun _ : Fin (n.len + 1) => (sectionsTerminalArrow (G.obj (op a)) L.leftOp).right)
    (fun _ => (sectionsTerminalArrow (G.obj (op a)) L.leftOp).hom)))

/-- The map out of the sections of a power induced by a cocone on the wide span of the sections
of the terminal arrow: transpose the legs through the adjunction and lift into the power. -/
noncomputable def powerSectionsDesc :
    (powerSections (G.obj (op a)) L.leftOp).obj n ⟶ s.pt :=
  (inv (adj.counit.app (op s.pt)) ≫ L.map (Pi.lift
    (f := fun _ : Fin (n.len + 1) => G.obj (op a))
    fun i => G.map ((s.ι.app (some i)).op ≫ adj.counit.app (op a)))).unop

/-- `Stacks.CechSite.powerSectionsDesc` restricts along the `i`-th projection of the power to
the `i`-th leg of the cocone. -/
lemma powerSectionsIncl_comp_powerSectionsDesc (i : Fin (n.len + 1)) :
    powerSectionsIncl (G.obj (op a)) L.leftOp n i ≫ powerSectionsDesc adj a n s =
      s.ι.app (some i) := by
  have hc : L.map (G.map ((s.ι.app (some i)).op ≫ adj.counit.app (op a))) =
      adj.counit.app (op s.pt) ≫ (s.ι.app (some i)).op :=
    (cancel_mono (adj.counit.app (op a))).1
      ((adj.counit_naturality ((s.ι.app (some i)).op ≫ adj.counit.app (op a))).trans
        (Category.assoc _ _ _).symm)
  have hop : (inv (adj.counit.app (op s.pt)) ≫ L.map (Pi.lift
          (f := fun _ : Fin (n.len + 1) => G.obj (op a))
          fun j => G.map ((s.ι.app (some j)).op ≫ adj.counit.app (op a)))) ≫
        L.map (Pi.π (fun _ : Fin (n.len + 1) => G.obj (op a)) i) =
      (s.ι.app (some i)).op := by
    rw [Category.assoc, ← L.map_comp, Pi.lift_comp_π, hc, IsIso.inv_hom_id_assoc]
  exact Quiver.Hom.op_inj hop

end Desc

/-- Under an adjunction whose right adjoint is fully faithful and preserves limits, the
sections of the powers of an object in the image of the right adjoint are the wide pushout of
its sections under the sections of the terminal object. -/
noncomputable def isColimitPowerSectionsCoconeOfAdjunction (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : A) (n : SimplexCategory) :
    IsColimit (powerSectionsCocone (G.obj (op a)) L.leftOp n) where
  desc s := powerSectionsDesc adj a n s
  fac s j := by
    obtain _ | i := j
    · obtain ⟨i⟩ : Nonempty (Fin (n.len + 1)) := ⟨0⟩
      change powerSectionsHead (G.obj (op a)) L.leftOp n ≫ _ = _
      rw [← arrow_comp_powerSectionsIncl (G.obj (op a)) L.leftOp n i, Category.assoc,
        powerSectionsIncl_comp_powerSectionsDesc]
      exact s.w (WidePushoutShape.Hom.init i)
    · exact powerSectionsIncl_comp_powerSectionsDesc adj a n s i
  uniq s φ hφ :=
    hom_ext_powerSectionsIncl adj a n fun i =>
      (hφ (some i)).trans (powerSectionsIncl_comp_powerSectionsDesc adj a n s i).symm

end Adjunction

/-! ### The Čech cosimplicial object of a one-member family -/

section Singleton

variable {C : Type u} [Category.{v} C] {T V : C} (h : V ⟶ T) [HasFiniteProducts (Over T)]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] (F : Cᵒᵖ ⥤ A)

/-- The projection of the Čech cosimplicial object of the one-member family `{V → T}` onto its
single factor, the sections over the power of `V`. -/
noncomputable def singletonCechProj (n : SimplexCategory) :
    (cechCosimplicialObject (PreZeroHypercover.singleton.{w} h) F).obj n ⟶
      (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).obj n :=
  Pi.π (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) =>
    (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).obj n) (fun _ => PUnit.unit)

/-- The section of `Stacks.CechSite.singletonCechProj` given by the diagonal. -/
noncomputable def singletonCechSect (n : SimplexCategory) :
    (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).obj n ⟶
      (cechCosimplicialObject (PreZeroHypercover.singleton.{w} h) F).obj n :=
  Pi.lift (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) => 𝟙 _)

/-- The diagonal section followed by the projection is the identity. -/
lemma singletonCechSect_comp_proj (n : SimplexCategory) :
    singletonCechSect h F n ≫ singletonCechProj.{w} h F n = 𝟙 _ := Pi.lift_comp_π _ _

/-- The projection followed by the diagonal section is the identity. -/
lemma singletonCechProj_comp_sect (n : SimplexCategory) :
    singletonCechProj.{w} h F n ≫ singletonCechSect h F n = 𝟙 _ := by
  refine Pi.hom_ext _ _ (fun i => ?_)
  obtain rfl : (fun _ : Fin (n.len + 1) => PUnit.unit) = i := Subsingleton.elim _ _
  calc (singletonCechProj.{w} h F n ≫ singletonCechSect h F n) ≫ singletonCechProj.{w} h F n
      = singletonCechProj.{w} h F n ≫ (singletonCechSect h F n ≫ singletonCechProj.{w} h F n) :=
        Category.assoc _ _ _
    _ = singletonCechProj.{w} h F n ≫ 𝟙 _ := by rw [singletonCechSect_comp_proj]
    _ = singletonCechProj.{w} h F n := Category.comp_id _
    _ = 𝟙 _ ≫ singletonCechProj.{w} h F n := (Category.id_comp _).symm

/-- The projection is natural in the simplex category: a cosimplicial structure map of the
Čech cosimplicial object of a one-member family is, on the single factor, the restriction
along the reindexing map of the power. -/
lemma singletonCechProj_naturality {n m : SimplexCategory} (g : n ⟶ m) :
    (cechCosimplicialObject (PreZeroHypercover.singleton.{w} h) F).map g ≫
        singletonCechProj.{w} h F m =
      singletonCechProj.{w} h F n ≫
        (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).map g := by
  change (Pi.lift (fun i : Fin (m.len + 1) → PUnit.{w + 1} =>
      Pi.π (fun _ : (Fin (n.len + 1) → PUnit.{w + 1}) =>
          (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).obj n)
        (fun a => i (g.toOrderHom a)) ≫
        (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).map g)) ≫
      Pi.π (fun _ : (Fin (m.len + 1) → PUnit.{w + 1}) =>
        (powerSections (Over.mk h) ((Over.forget T).op ⋙ F)).obj m) (fun _ => PUnit.unit) = _
  exact Pi.lift_comp_π _ _

/-- The projection, as a morphism of cosimplicial objects. -/
noncomputable def singletonCechProjNatTrans :
    cechCosimplicialObject (PreZeroHypercover.singleton.{w} h) F ⟶
      powerSections (Over.mk h) ((Over.forget T).op ⋙ F) where
  app n := singletonCechProj.{w} h F n
  naturality _ _ g := singletonCechProj_naturality.{w} h F g

/-- The projection onto the single factor is an isomorphism. -/
lemma isIso_singletonCechProj (n : SimplexCategory) :
    IsIso (singletonCechProj.{w} h F n) :=
  ⟨singletonCechSect h F n, singletonCechProj_comp_sect.{w} h F n,
    singletonCechSect_comp_proj.{w} h F n⟩

/-- The Čech cosimplicial object of the one-member family `{V → T}` is the sections of the
powers of `V` over `T`. -/
noncomputable def singletonCechCosimplicialIso :
    cechCosimplicialObject (PreZeroHypercover.singleton.{w} h) F ≅
      powerSections (Over.mk h) ((Over.forget T).op ⋙ F) :=
  haveI : ∀ n, IsIso ((singletonCechProjNatTrans.{w} h F).app n) :=
    fun n => isIso_singletonCechProj.{w} h F n
  haveI : IsIso (singletonCechProjNatTrans.{w} h F) := NatIso.isIso_of_isIso_app _
  asIso (singletonCechProjNatTrans.{w} h F)

end Singleton

end Stacks.CechSite

/-! ### The comparison with the Amitsur complex -/

namespace Stacks.Descent

open Stacks.CechSite

/-- The coefficient functor `S ↦ S ⊗[R] M` of the Amitsur complex, from commutative algebras
over the lifted base ring to `R`-modules. -/
noncomputable abbrev amitsurCoefficients (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommGroup M] [Module R M] :
    CommAlgCat.{max uR uA} (ULift.{uA} R) ⥤ ModuleCat.{max uR uA uM} R :=
  tensorModuleFunctor (ULift.{uA} R) M ⋙
    ModuleCat.restrictScalars (algebraMap R (ULift.{uA} R))

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- The cosimplicial module `(A/R)_• ⊗_R M` underlying the Amitsur complex is the Čech conerve
of the algebra map composed with the coefficient functor. -/
lemma amitsurAugmentation_right :
    (amitsurAugmentation R A M).right =
      (algebraMapArrow R A).cechConerve ⋙ amitsurCoefficients.{uR, uA, uM} R M := rfl

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {T V : C} (h : V ⟶ T)
  (F : Cᵒᵖ ⥤ ModuleCat.{max uR uA uM} R)
  (Γ : (Over T)ᵒᵖ ⥤ CommAlgCat.{max uR uA} (ULift.{uA} R))

/-- The Čech cosimplicial object of a one-member covering `{V → T}` is `(A/R)_• ⊗_R M`, given
that the presheaf `ℱ` is, on the slice over `T`, the base change `Γ(-, 𝒪) ⊗_R M` (`hcoeff`), that
the arrow `Γ(T, 𝒪) ⟶ Γ(V, 𝒪)` is the algebra map `R → A` (`harrow`), and that the degreewise
comparison maps are isomorphisms (`hiso`). -/
noncomputable def cechCosimplicialObjectIsoAmitsur
    (hcoeff : (Over.forget T).op ⋙ F ≅ Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) :
    cechCosimplicialObject (PreZeroHypercover.singleton.{max uR uA uM} h) F ≅
      (amitsurAugmentation R A M).right :=
  singletonCechCosimplicialIso.{max uR uA uM} h F ≪≫
    Functor.isoWhiskerLeft (cechNerveTerminalFrom (Over.mk h)).rightOp hcoeff ≪≫
      Functor.isoWhiskerRight (conerveSectionsIso (Over.mk h) Γ hiso).symm
          (amitsurCoefficients.{uR, uA, uM} R M) ≪≫
        Functor.isoWhiskerRight (CosimplicialObject.cechConerve.mapIso harrow)
          (amitsurCoefficients.{uR, uA, uM} R M)

/-- The Čech complex of a one-member covering `{V → T}` is `s((A/R)_• ⊗_R M)`, termwise and
differentialwise, under the hypotheses of `Stacks.Descent.cechCosimplicialObjectIsoAmitsur`. -/
noncomputable def cechComplexSingletonIsoAmitsur
    (hcoeff : (Over.forget T).op ⋙ F ≅ Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) :
    cechComplex (PreZeroHypercover.singleton.{max uR uA uM} h) F ≅
      amitsurCochainComplex R A M :=
  cechComplexIsoOfCosimplicialIso (PreZeroHypercover.singleton.{max uR uA uM} h) F
    (cechCosimplicialObjectIsoAmitsur h F Γ hcoeff harrow hiso)

/-- For `A` faithfully flat over `R`, the Čech cohomology of `{V → T}` with coefficients in a
presheaf whose sections are the base change `Γ(-, 𝒪) ⊗_R M` vanishes in every positive degree,
under the hypotheses of `Stacks.Descent.cechCosimplicialObjectIsoAmitsur`. -/
theorem isZero_cechCohomology_singleton_succ_of_conerveSectionsIso [Module.FaithfullyFlat R A]
    (hcoeff : (Over.forget T).op ⋙ F ≅ Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max uR uA uM} h) F (p + 1)) :=
  isZero_cechCohomology_singleton_succ h F
    (cechCosimplicialObjectIsoAmitsur h F Γ hcoeff harrow hiso) p

/-- For a finite family `{U_i → T}` in a finitary extensive category and a finite-product
preserving presheaf whose sections on the slice are the base change `Γ(-, 𝒪) ⊗_R M` along a
faithfully flat `R → A`, the Čech cohomology vanishes in every positive degree, under the
hypotheses of `Stacks.Descent.cechCosimplicialObjectIsoAmitsur` for the one-member family
`{∐ U_i → T}`. -/
theorem isZero_cechCohomology_succ_of_conerveSectionsIso [FinitaryExtensive C]
    (E : PreZeroHypercover.{max uR uA uM} T) [Finite E.I₀]
    (F : Cᵒᵖ ⥤ ModuleCat.{max uR uA uM} R) [PreservesFiniteProducts F]
    (Γ : (Over T)ᵒᵖ ⥤ CommAlgCat.{max uR uA} (ULift.{uA} R)) [Module.FaithfullyFlat R A]
    (hcoeff : (Over.forget T).op ⋙ F ≅ Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk (Sigma.desc E.f)) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory,
      IsIso (conerveSectionsMap (Over.mk (Sigma.desc E.f)) Γ n)) (p : ℕ) :
    IsZero (cechCohomology E F (p + 1)) :=
  isZero_cechCohomology_succ_of_singletonCosimplicialIso E F
    (cechCosimplicialObjectIsoAmitsur (Sigma.desc E.f) F Γ hcoeff harrow hiso) p

/-- The variant of
`Stacks.Descent.isZero_cechCohomology_singleton_succ_of_conerveSectionsIso` whose termwise
hypothesis is stated as a colimit: in every degree, the sections of the power
`V ×_T ⋯ ×_T V` are the wide pushout of `p + 1` copies of the sections of `V` under the
sections of `T`. -/
theorem isZero_cechCohomology_singleton_succ_of_isColimit [Module.FaithfullyFlat R A]
    (hcoeff : (Over.forget T).op ⋙ F ≅ Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hcolim : ∀ n : SimplexCategory, IsColimit (powerSectionsCocone (Over.mk h) Γ n))
    (p : ℕ) :
    IsZero (cechCohomology (PreZeroHypercover.singleton.{max uR uA uM} h) F (p + 1)) :=
  isZero_cechCohomology_singleton_succ_of_conerveSectionsIso h F Γ hcoeff harrow
    (fun n => isIso_conerveSectionsMap (Over.mk h) Γ n (hcolim n)) p

/-- The variant of `Stacks.Descent.cechCosimplicialObjectIsoAmitsur` whose coefficient
hypothesis `hpow` identifies the sections with the base change `Γ(-, 𝒪) ⊗_R M` only on the fibre
powers `V ×_T ⋯ ×_T V`. -/
noncomputable def cechCosimplicialObjectIsoAmitsurOfPowerSections
    (hpow : powerSections (Over.mk h) ((Over.forget T).op ⋙ F) ≅
      powerSections (Over.mk h) Γ ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (Over.mk h) Γ ≅ algebraMapArrow R A)
    (hiso : ∀ n : SimplexCategory, IsIso (conerveSectionsMap (Over.mk h) Γ n)) :
    cechCosimplicialObject (PreZeroHypercover.singleton.{max uR uA uM} h) F ≅
      (amitsurAugmentation R A M).right :=
  singletonCechCosimplicialIso.{max uR uA uM} h F ≪≫ hpow ≪≫
    Functor.isoWhiskerRight (conerveSectionsIso (Over.mk h) Γ hiso).symm
        (amitsurCoefficients.{uR, uA, uM} R M) ≪≫
      Functor.isoWhiskerRight (CosimplicialObject.cechConerve.mapIso harrow)
        (amitsurCoefficients.{uR, uA, uM} R M)

section Adjunction

variable {L : Over T ⥤ (CommAlgCat.{max uR uA} (ULift.{uA} R))ᵒᵖ}
  {G : (CommAlgCat.{max uR uA} (ULift.{uA} R))ᵒᵖ ⥤ Over T}

/-- For `A` faithfully flat over `R` and an object `G a` in the image of a fully faithful,
limit-preserving right adjoint, the higher Čech cohomology of the one-member covering `{G a → T}`
vanishes, given the coefficient comparison `hpow` on the fibre powers and the arrow
identification `harrow`. -/
theorem isZero_cechCohomology_singleton_succ_of_adjunction_of_powerSections
    [Module.FaithfullyFlat R A] (adj : L ⊣ G) [G.Full] [G.Faithful]
    [PreservesLimitsOfSize.{0, 0} G] (a : CommAlgCat.{max uR uA} (ULift.{uA} R))
    (hpow : powerSections (G.obj (op a)) ((Over.forget T).op ⋙ F) ≅
      powerSections (G.obj (op a)) L.leftOp ⋙ amitsurCoefficients.{uR, uA, uM} R M)
    (harrow : sectionsTerminalArrow (G.obj (op a)) L.leftOp ≅ algebraMapArrow R A) (p : ℕ) :
    IsZero (cechCohomology
      (PreZeroHypercover.singleton.{max uR uA uM} (G.obj (op a)).hom) F (p + 1)) :=
  isZero_cechCohomology_singleton_succ (G.obj (op a)).hom F
    (cechCosimplicialObjectIsoAmitsurOfPowerSections (G.obj (op a)).hom F L.leftOp hpow harrow
      (fun n => isIso_conerveSectionsMap _ _ n
        (isColimitPowerSectionsCoconeOfAdjunction adj a n))) p

end Adjunction

end Stacks.Descent

end
