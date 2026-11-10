module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.ExtTowerVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FreeCechComplexOfACover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyReduction

/-!
# The vanishing input of Stacks 0GN3

Let `S` be a set of sheaves of sets on a small site satisfying hypotheses (1) and (2) of
Stacks 0GN3, and let `G` be a filtered diagram of injective abelian sheaves. Write `Y = colim G`
and `**Z**_X^♯` for the free abelian sheaf on a sheaf of sets `X`. If for every `K ∈ S` and every
`r` the functors `Ext^q(**Z**_{K^r}^♯, -)` commute with the colimit for `q ≤ n` (the hypothesis
`hlocal`), then `H^{n+1}(C, Y) = 0`. This is the input that
`isIso_colimit_post_rightDerived_globalSections_of_acyclic` needs to prove Stacks 0GN3.

A class in `Ext^{n+1}(**Z**^♯, Y)` restricts to zero on `**Z**_K^♯` for some `K ∈ S` surjecting
onto the final sheaf, and the free abelian Čech complex of `K ⟶ *`, whose degree-`i` term is
`**Z**_{K^{i+1}}^♯`, resolves `**Z**^♯` (Stacks 01GB, 01GC). The dévissage
`ext_eq_zero_of_exact_tower` along its opcycles then kills the class.

The hypothesis `hlocal` is the localization comparison of Stacks 07A0 together with the inductive
hypothesis of Stacks 0GN3 on the localized sites `C/K^r`; it is assumed here, so no declaration in
this file carries the tag 0GN3.

## Main results

* `Stacks.Cohomology.ColimitsOfCohomology.exists_mem_coveringSet_ext_restriction_eq_zero`: a class
  in `Ext^{n+1}(**Z**^♯, M)` is annihilated by restriction along `**Z**_K^♯ ⟶ **Z**^♯` for some
  `K ∈ S` surjecting onto the final sheaf.
* `Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_coveringSet`: granting `hlocal`, every
  class in `Ext^{n+1}(**Z**^♯, colim G)` vanishes.
* `Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_isIso`:
  the same statement in the form
  `IsZero (((Sheaf.Γ J Ab).rightDerived (n + 1)).obj (colimit G))`.
* `Stacks.Cohomology.ColimitsOfCohomology.ext_eq_zero_of_coveringSet_of_acyclic` and
  `Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_acyclic`:
  the two previous statements with pointwise injectivity of `G` replaced by acyclicity of each
  `G j` against the free abelian sheaves on the self powers of the members of `S`, and for global
  sections in degree `n + 1`.
* `Stacks.Cohomology.ColimitsOfCohomology`
  `.isZero_rightDerived_globalSections_colimit_of_vanishesOnObjects`: the same vanishing when each
  `G j` satisfies condition (1) of Stacks 07A1 and the sheaves of sets involved are representable.
  This holds for an inverse image of an injective sheaf (Stacks 0D6X), which need not be
  injective.
* `Stacks.Cohomology.ColimitsOfCohomology`
  `.isIso_colimit_post_rightDerived_globalSections_of_isIso_colimit_post_ext`: Stacks 0GN3 in
  every degree from hypotheses (1), (2), (3), (5) and `hlocal`.

## Implementation notes

`CategoryTheory.Sheaf.composeAndSheafify J AddCommGrpCat.free` and
`CategoryTheory.Presheaf.freeAbelianSheaf J` applied to the underlying presheaf are definitionally
the same functor. The statements here use the second, which is the one of the Čech resolution,
while the adjunction with the underlying sheaf of sets is stated for the first.

The site, the coefficients and the index category of the diagram all live in one universe `u`.

## References

* [Stacks Project, Tag 0GN3](https://stacks.math.columbia.edu/tag/0GN3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.ColimitsOfCohomology

attribute [local instance] ColimitsOfCohomology.enoughInjectives_sheaf_ab
  ColimitsOfCohomology.additive_globalSections_ab

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-! ### Restricting an `Ext` class to a member of the covering set -/

/-- A class annihilated by restriction along `g` is annihilated by restriction along any
composite ending in `g`. -/
public lemma ext_comp_eq_zero_of_comp {A : Type*} [Category* A] [Abelian A] [HasExt.{u} A]
    {W X Y Z : A} (f : W ⟶ X) (g : X ⟶ Y) {n : ℕ} (e : Abelian.Ext.{u} Y Z n)
    (h : (Abelian.Ext.mk₀ g).comp e (zero_add n) = 0) :
    (Abelian.Ext.mk₀ (f ≫ g)).comp e (zero_add n) = 0 := by
  rw [← Abelian.Ext.mk₀_comp_mk₀_assoc, h, Abelian.Ext.comp_zero]

/-- Every class in `Ext^{n+1}(X, Y)` is annihilated by restriction along some epimorphism
onto `X`. -/
private lemma exists_epi_comp_ext_eq_zero {A : Type*} [Category* A] [Abelian A]
    [HasExt.{u} A] [HasInjectiveResolutions A] {X Y : A} (n : ℕ)
    (e : Abelian.Ext.{u} X Y (n + 1)) :
    ∃ (P : A) (p : P ⟶ X), Epi p ∧ (Abelian.Ext.mk₀ p).comp e (zero_add _) = 0 := by
  let I := injectiveResolution Y
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective e (n + 2) rfl
  obtain ⟨P, p, hp, g, hg⟩ := (I.exact_succ n).exact_up_to_refinements f hf
  refine ⟨P, p, hp, ?_⟩
  rw [I.mk₀_comp_extMk, I.extMk_eq_zero_iff _ _ _ _ n rfl]
  exact ⟨g, hg.symm⟩

/-- **Stacks 0GN3, hypotheses (1) and (2), on `Ext`.** Let `S` be a set of sheaves of sets
containing a member which surjects onto the final sheaf, and such that a surjection onto a member
of `S` admits a map from a member of `S` with surjective composite. Then every class in
`Ext^{n+1}(**Z**^♯, M)` is annihilated by restriction along `**Z**_K^♯ ⟶ **Z**^♯` for some `K ∈ S`
which surjects onto the final sheaf. -/
public lemma exists_mem_coveringSet_ext_restriction_eq_zero (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (M : Sheaf J Ab.{u}) (n : ℕ)
    (e : Abelian.Ext.{u}
      ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj) M (n + 1)) :
    ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K) ∧
      (Abelian.Ext.mk₀ ((Presheaf.freeAbelianSheaf J).map (terminal.from K).hom)).comp e
        (zero_add _) = 0 := by
  let L := Sheaf.composeAndSheafify J AddCommGrpCat.free
  let U := sheafForget (D := Ab.{u}) J
  let adj := Sheaf.adjunction J AddCommGrpCat.adj
  let T := ⊤_ (Sheaf J (Type u))
  let e' : Abelian.Ext.{u} (L.obj T) M (n + 1) := e
  obtain ⟨P, f, hf, he⟩ := exists_epi_comp_ext_eq_zero n e'
  have hlf : Sheaf.IsLocallySurjective f := (Sheaf.isLocallySurjective_iff_epi' Ab.{u} f).2 hf
  have hUf : Sheaf.IsLocallySurjective (U.map f) := inferInstance
  let Q := pullback (U.map f) (adj.unit.app T)
  have hQ : Sheaf.IsLocallySurjective (terminal.from Q) := by
    have hq : Sheaf.IsLocallySurjective (pullback.snd (U.map f) (adj.unit.app T)) := by
      exact CoveringSet.isLocallySurjective_of_exists_lift J _ (U.map f) (adj.unit.app T) hUf
        (fun Z a b hab => ⟨pullback.lift a b hab, pullback.lift_snd a b hab⟩)
    rwa [show pullback.snd (U.map f) (adj.unit.app T) = terminal.from Q from
      terminal.hom_ext _ _] at hq
  obtain ⟨K, hK, ⟨g⟩, hg⟩ :=
    Sheaf.exists_mem_hom_isLocallySurjective_terminal_of_coveringSet h_terminal h_lift Q hQ
  let v : K ⟶ U.obj P := g ≫ pullback.fst (U.map f) (adj.unit.app T)
  let m : L.obj K ⟶ P := (adj.homEquiv K P).symm v
  have hv : v ≫ U.map f = terminal.from K ≫ adj.unit.app T := by
    dsimp only [v]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact terminal.hom_ext _ _
  have hm : m ≫ f = L.map (terminal.from K) := by
    apply (adj.homEquiv K (L.obj T)).injective
    rw [adj.homEquiv_naturality_right]
    change adj.homEquiv K P ((adj.homEquiv K P).symm v) ≫ U.map f = _
    rw [Equiv.apply_symm_apply, hv, adj.homEquiv_unit]
    exact adj.unit.naturality (terminal.from K)
  refine ⟨K, hK, hg, ?_⟩
  change (Abelian.Ext.mk₀ (L.map (terminal.from K))).comp e' (zero_add _) = 0
  rw [← hm]
  exact ext_comp_eq_zero_of_comp m f e' he

/-! ### The free abelian sheaf on the final sheaf -/

/-- The free abelian sheaf on the final sheaf of sets is the constant sheaf `**Z**^♯`. -/
public def freeAbelianSheafTerminalIsoConstantSheaf :
    (Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj ≅
      (constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)) := by
  let T := ⊤_ (Sheaf J (Type u))
  letI (W : Cᵒᵖ) : Unique (T.obj.obj W) :=
    Types.isTerminalEquivUnique _
      (terminalIsTerminal.isTerminalObj
        (sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj W) _)
  let e (W : Cᵒᵖ) : AddCommGrpCat.free.obj (T.obj.obj W) ≅ AddCommGrpCat.of (ULift.{u} ℤ) :=
    ((FreeAbelianGroup.uniqueEquiv _).trans AddEquiv.ulift.symm).toAddCommGrpIso
  let eP : T.obj ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) :=
    NatIso.ofComponents e (by
      intro W V f
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro t
      change (e V).hom (FreeAbelianGroup.map (T.obj.map f) (FreeAbelianGroup.of t)) =
        (e W).hom (FreeAbelianGroup.of t)
      simp only [FreeAbelianGroup.map_of_apply]
      change AddEquiv.ulift.symm ((FreeAbelianGroup.uniqueEquiv _)
          (FreeAbelianGroup.of ((T.obj.map f) t))) =
        AddEquiv.ulift.symm ((FreeAbelianGroup.uniqueEquiv _) (FreeAbelianGroup.of t))
      simp [FreeAbelianGroup.uniqueEquiv])
  exact (presheafToSheaf J Ab.{u}).mapIso eP

/-! ### The vanishing -/

variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- The free abelian Čech complex of `K ⟶ *`. -/
private abbrev freeCech (K : Sheaf J (Type u)) :=
  (SimplicialObject.freeAbelianSheafComplexFunctor J).obj (Arrow.mk (terminal.from K).hom).cechNerve

/-- The functor `Hom(-, Y)` commutes with the colimit on the degree-`i` term of the free Čech
complex as soon as `Ext^0(**Z**_{K^{i+1}}^♯, -)` does. -/
private lemma isIso_colimit_post_freeCech_obj (K : Sheaf J (Type u)) {I : Type u}
    [SmallCategory I] [IsFiltered I] (G : I ⥤ Sheaf J Ab.{u}) (i : ℕ)
    (h0 : IsIso (colimit.post G (Abelian.extFunctorObj.{u}
      ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K (i + 1)).obj) 0))) :
    IsIso (colimit.post G (preadditiveCoyoneda.obj (op ((freeCech J K).X i)))) := by
  have h1 : IsIso (colimit.post G (preadditiveCoyoneda.obj
      (op ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K (i + 1)).obj)))) :=
    isIso_colimit_post_of_iso G (ModuleSheafCohomology.extZeroIsoCoyoneda _)
  exact isIso_colimit_post_of_iso G
    (preadditiveCoyoneda.mapIso (CoveringSet.freeCechObjIso J K i).op)

/-- The opcycles of the free Čech complex of a covering `K ⟶ *` sit in short exact sequences. -/
private lemma shortExact_freeCech_opcycles {K : Sheaf J (Type u)}
    (hf : Sheaf.IsLocallySurjective (terminal.from K)) (i : ℕ) :
    (ShortComplex.mk ((freeCech J K).fromOpcycles (i + 1) i) ((freeCech J K).pOpcycles i)
      (fromOpcycles_comp_pOpcycles (freeCech J K) i)).ShortExact :=
  shortExact_opcycles_of_exactAt _ i
    (CoveringSet.freeCechExactAt J (terminal.from K) hf (i + 1) (by omega))

/-- A class in `Ext^{n+1}(**Z**^♯, Y)` killed by restriction along `**Z**_K^♯ ⟶ **Z**^♯` vanishes
if the free Čech complex of `K ⟶ *` satisfies the vanishing and extension hypotheses of the
dévissage. -/
private lemma ext_eq_zero_of_freeCech_tower {K : Sheaf J (Type u)}
    (hf : Sheaf.IsLocallySurjective (terminal.from K)) {Y : Sheaf J Ab.{u}} (n : ℕ)
    (hv : ∀ i q : ℕ, 0 < i → 0 < q → i + q = n + 1 →
      ∀ a : Abelian.Ext.{u} ((freeCech J K).X i) Y q, a = 0)
    (hext : ∀ a : (freeCech J K).opcycles (n + 1) ⟶ Y,
      ∃ b : (freeCech J K).X n ⟶ Y, (freeCech J K).fromOpcycles (n + 1) n ≫ b = a)
    (e : Abelian.Ext.{u} ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj) Y (n + 1))
    (hkill : (Abelian.Ext.mk₀ ((Presheaf.freeAbelianSheaf J).map (terminal.from K).hom)).comp e
      (zero_add _) = 0) : e = 0 := by
  let X := freeCech J K
  let E : X.opcycles 0 ≅
      (Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj :=
    CoveringSet.freeCechOpcyclesZeroIso J (terminal.from K) hf
  let eX : Abelian.Ext.{u} (X.opcycles 0) Y (n + 1) :=
    (Abelian.Ext.mk₀ E.hom).comp e (zero_add _)
  have he : (Abelian.Ext.mk₀ (X.pOpcycles 0)).comp eX (zero_add _) = 0 := by
    refine (Abelian.Ext.mk₀_comp_mk₀_assoc (X.pOpcycles 0) E.hom e).trans ?_
    rw [CoveringSet.pOpcycles_comp_freeCechOpcyclesZeroIso_hom J (terminal.from K) hf]
    exact ext_comp_eq_zero_of_comp _ _ e hkill
  have hX : eX = 0 :=
    ext_eq_zero_of_exact_tower (fun i => X.opcycles i) (fun i => X.X i)
      (fun i => X.fromOpcycles (i + 1) i) (fun i => X.pOpcycles i)
      (fromOpcycles_comp_pOpcycles X) (shortExact_freeCech_opcycles J hf) Y n hv hext eX he
  simpa only [eX, Abelian.Ext.mk₀_comp_mk₀_assoc, E.inv_hom_id, Abelian.Ext.mk₀_id_comp,
    Abelian.Ext.comp_zero] using
    congrArg (fun a : Abelian.Ext.{u} (X.opcycles 0) Y (n + 1) =>
      (Abelian.Ext.mk₀ E.inv).comp a (zero_add _)) hX

/-- If every class in `Ext^{n+1}(**Z**^♯, M)` vanishes, then so does `H^{n+1}(C, M)`. -/
private lemma isZero_rightDerived_globalSections_of_ext_eq_zero (M : Sheaf J Ab.{u}) (n : ℕ)
    (h : ∀ e : Abelian.Ext.{u}
      ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj) M (n + 1), e = 0) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj M) := by
  have hZ (e : Abelian.Ext.{u}
      ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) M (n + 1)) : e = 0 :=
    ext_eq_zero_of_iso_first (freeAbelianSheafTerminalIsoConstantSheaf J).symm (n + 1) h e
  have hExt : IsZero ((Sheaf.functorH J (n + 1)).obj M) := by
    change IsZero (AddCommGrpCat.of (Abelian.Ext.{u}
      ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) M (n + 1)))
    have : Subsingleton (Abelian.Ext.{u}
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) M (n + 1)) :=
      ⟨fun a b => (hZ a).trans (hZ b).symm⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact hExt.of_iso ((globalSectionsRightDerivedIsoFunctorH J (n + 1)).app M)

/-- **The vanishing input of Stacks 0GN3, on `Ext` out of the free abelian sheaf on the final
sheaf.** Let `S` satisfy hypotheses (1) and (2) of Stacks 0GN3, let `G` be a filtered diagram of
injective abelian sheaves, and suppose that for every `K ∈ S` and every `r` the functors
`Ext^q(**Z**_{K^r}^♯, -)` commute with colimits of shape `I` for all `q ≤ n`. Then every class in
`Ext^{n+1}(**Z**^♯, colim G)` vanishes. -/
public lemma ext_eq_zero_of_coveringSet (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (n : ℕ) (G : I ⥤ Sheaf J Ab.{u}) (hG : ∀ i, Injective (G.obj i))
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), q < n + 1 → ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q)))
    (e : Abelian.Ext.{u} ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj)
      (colimit G) (n + 1)) : e = 0 := by
  obtain ⟨K, hK, hf, hkill⟩ :=
    exists_mem_coveringSet_ext_restriction_eq_zero J S h_terminal h_lift (colimit G) n e
  have hterm (i : ℕ) : IsIso (colimit.post G (preadditiveCoyoneda.obj (op ((freeCech J K).X i)))) :=
    isIso_colimit_post_freeCech_obj J K G i (hlocal K hK (i + 1) 0 (by omega) G)
  refine ext_eq_zero_of_freeCech_tower J hf n (fun i q hi hq hiq a => ?_) (fun a => ?_) e hkill
  · obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have := hlocal K hK (i + 1) (q' + 1) (by omega) G
    have hz : IsZero ((Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K (i + 1)).obj)
          (q' + 1)).obj (colimit G)) :=
      isZero_extFunctorObj_colimit_of_injective _ q' G hG
    exact ext_eq_zero_of_iso_first (CoveringSet.freeCechObjIso J K i) (q' + 1)
      (fun _ => (AddCommGrpCat.subsingleton_of_isZero hz).elim _ 0) a
  · have := hterm (n + 1)
    have := hterm (n + 2)
    exact exists_extension_of_opcycles_filtered_colimit _ n
      (CoveringSet.freeCechExactAt J (terminal.from K) hf (n + 1) (by omega)) G hG a

/-- **The vanishing input of Stacks 0GN3.** Let `S` satisfy hypotheses (1) and (2) of Stacks 0GN3,
let `G` be a filtered diagram of injective abelian sheaves, and suppose that for every `K ∈ S` and
every `r` the functors `Ext^q(**Z**_{K^r}^♯, -)` commute with colimits of shape `I` for all
`q ≤ n`. Then degree-`n + 1` cohomology of the site vanishes on `colim G`. -/
public lemma isZero_rightDerived_globalSections_colimit_of_isIso (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (n : ℕ) (G : I ⥤ Sheaf J Ab.{u}) (hG : ∀ i, Injective (G.obj i))
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), q < n + 1 → ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q))) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit G)) :=
  isZero_rightDerived_globalSections_of_ext_eq_zero J _ n
    (ext_eq_zero_of_coveringSet J S h_terminal h_lift n G hG hlocal)

/-! ### The same vanishing from acyclicity of the stages

Pointwise injectivity of `G` is replaced by two hypotheses: `hGloc`, that each `G j` is acyclic
against the free abelian sheaves on the self powers of the members of `S`, and `hGglob`, that each
`G j` is acyclic in the one degree `n + 1`. Both follow from injectivity, and both can hold for a
diagram of inverse images of injective sheaves, which need not be injective. -/

/-- **The vanishing input of Stacks 0GN3, from acyclicity of the diagram rather than pointwise
injectivity.** The hypotheses on `S` and the hypothesis `hlocal` are those of
`ext_eq_zero_of_coveringSet`; pointwise injectivity of `G` is replaced by `hGloc`, acyclicity of
each `G j` against `**Z**_{K^r}^♯` in positive degrees, and `hGglob`, vanishing of
`Ext^{n+1}(**Z**^♯, G j)`. -/
public lemma ext_eq_zero_of_coveringSet_of_acyclic (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (n : ℕ) (G : I ⥤ Sheaf J Ab.{u})
    (hGloc : ∀ K ∈ S, ∀ (r q : ℕ), 0 < q → ∀ j : I, IsZero ((Abelian.extFunctorObj.{u}
      ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q).obj (G.obj j)))
    (hGglob : ∀ j : I, ∀ a : Abelian.Ext.{u}
      ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj) (G.obj j) (n + 1), a = 0)
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), q < n + 1 → ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q)))
    (e : Abelian.Ext.{u} ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj)
      (colimit G) (n + 1)) : e = 0 := by
  obtain ⟨K, hK, hf, hkill⟩ :=
    exists_mem_coveringSet_ext_restriction_eq_zero J S h_terminal h_lift (colimit G) n e
  have hterm (i : ℕ) : IsIso (colimit.post G (preadditiveCoyoneda.obj (op ((freeCech J K).X i)))) :=
    isIso_colimit_post_freeCech_obj J K G i (hlocal K hK (i + 1) 0 (by omega) G)
  refine ext_eq_zero_of_freeCech_tower J hf n (fun i q hi hq hiq a => ?_) (fun a => ?_) e hkill
  · obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have := hlocal K hK (i + 1) (q' + 1) (by omega) G
    have hz : IsZero ((Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K (i + 1)).obj)
          (q' + 1)).obj (colimit G)) :=
      isZero_extFunctorObj_colimit_of_isZero _ (q' + 1) G
        (fun j => hGloc K hK (i + 1) (q' + 1) (by omega) j)
    exact ext_eq_zero_of_iso_first (CoveringSet.freeCechObjIso J K i) (q' + 1)
      (fun _ => (AddCommGrpCat.subsingleton_of_isZero hz).elim _ 0) a
  · have := hterm (n + 1)
    have := hterm (n + 2)
    exact exists_extension_of_opcycles_filtered_colimit_of_extension _ n G
      (fun j c => exists_extension_of_exact_tower_of_ext_eq_zero
        (fun i => (freeCech J K).opcycles i) (fun i => (freeCech J K).X i)
        (fun i => (freeCech J K).fromOpcycles (i + 1) i) (fun i => (freeCech J K).pOpcycles i)
        (fromOpcycles_comp_pOpcycles _) (shortExact_freeCech_opcycles J hf) (G.obj j) n
        (fun i q hq b => ext_eq_zero_of_iso_first (CoveringSet.freeCechObjIso J K i) q
          (fun _ => (AddCommGrpCat.subsingleton_of_isZero (hGloc K hK (i + 1) q hq j)).elim _ 0)
          b)
        (ext_eq_zero_of_iso_first (CoveringSet.freeCechOpcyclesZeroIso J (terminal.from K) hf)
          (n + 1) (hGglob j)) c) a

/-- **The vanishing input of Stacks 0GN3, from acyclicity of the diagram**, in the derived-functor
spelling: `hGglob` says that each `G j` is acyclic for global sections in degree `n + 1`. -/
public lemma isZero_rightDerived_globalSections_colimit_of_acyclic (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (n : ℕ) (G : I ⥤ Sheaf J Ab.{u})
    (hGloc : ∀ K ∈ S, ∀ (r q : ℕ), 0 < q → ∀ j : I, IsZero ((Abelian.extFunctorObj.{u}
      ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q).obj (G.obj j)))
    (hGglob : ∀ j : I, IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (G.obj j)))
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), q < n + 1 → ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q))) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit G)) := by
  have hGglob' (j : I) (a : Abelian.Ext.{u}
      ((Presheaf.freeAbelianSheaf J).obj (⊤_ (Sheaf J (Type u))).obj) (G.obj j) (n + 1)) :
      a = 0 := by
    have h1 : IsZero ((Abelian.extFunctorObj.{u}
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))
          (n + 1)).obj (G.obj j)) :=
      ((hGglob j).of_iso
          ((globalSectionsRightDerivedIsoFunctorH J (n + 1)).app (G.obj j)).symm).of_iso
        ((functorHIsoExtFunctorObj J (n + 1)).app (G.obj j))
    exact ext_eq_zero_of_iso_first (freeAbelianSheafTerminalIsoConstantSheaf J) (n + 1)
      (fun _ => (AddCommGrpCat.subsingleton_of_isZero h1).elim _ 0) a
  exact isZero_rightDerived_globalSections_of_ext_eq_zero J _ n
    (ext_eq_zero_of_coveringSet_of_acyclic J S h_terminal h_lift n G hGloc hGglob' hlocal)

/-- **The vanishing input of Stacks 0GN3 for a diagram satisfying condition (1) of Stacks 07A1.**
If every `G j` vanishes on objects — `H^p(U, G j) = 0` for `p > 0` and every object `U` of the
site — then the two acyclicity hypotheses of
`isZero_rightDerived_globalSections_colimit_of_acyclic` hold, provided the sheaves of sets they are
taken against are representable: `hpow` for the self powers of the members of `S`, `hterm` for the
final sheaf.

`hG` is `Stacks.Cohomology.VanishesOnObjects J (G j)`, condition (1) of Stacks 07A1, unfolded.
It holds for an inverse image of an injective sheaf (Stacks 0D6X,
`Stacks.Cohomology.DerivedLowerShriek.vanishesOnObjects_inverseImage`), which need not be
injective. -/
public lemma isZero_rightDerived_globalSections_colimit_of_vanishesOnObjects
    (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (n : ℕ) (G : I ⥤ Sheaf J Ab.{u})
    (hpow : ∀ K ∈ S, ∀ r : ℕ,
      ∃ U : C, Nonempty ((CoveringSet.sheafPower J K r).obj.RepresentableBy U))
    (hterm : ∃ U : C, Nonempty ((⊤_ (Sheaf J (Type u))).obj.RepresentableBy U))
    (hG : ∀ j : I, ∀ (U : C) (Q : Cᵒᵖ ⥤ Type u), Q.RepresentableBy U → ∀ p : ℕ, 1 ≤ p →
      Subsingleton (Abelian.Ext.{u} ((Presheaf.freeAbelianSheaf J).obj Q) (G.obj j) p))
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), q < n + 1 → ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q))) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived (n + 1)).obj (colimit G)) := by
  refine isZero_rightDerived_globalSections_colimit_of_acyclic J S h_terminal h_lift n G
    (fun K hK r q hq j => ?_) (fun j => ?_) hlocal
  · obtain ⟨U, ⟨hU⟩⟩ := hpow K hK r
    have hsub := hG j U _ hU q hq
    change IsZero (AddCommGrpCat.of (Abelian.Ext.{u}
      ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) (G.obj j) q))
    exact AddCommGrpCat.isZero_of_subsingleton _
  · obtain ⟨U, ⟨hU⟩⟩ := hterm
    have hsub0 := hG j U _ hU (n + 1) (by omega)
    exact isZero_rightDerived_globalSections_of_ext_eq_zero J _ n
      (fun _ => Subsingleton.elim _ 0)

/-- **Stacks 0GN3, granting the localization comparison.** Let `S` be a set of sheaves of sets
satisfying hypotheses (1), (2), (3) and (5) of Stacks 0GN3, and suppose that for every `K ∈ S`,
every `r` and every `q` the functor `Ext^q(**Z**_{K^r}^♯, -)` commutes with filtered colimits of
shape `I`. Then degree-`p` cohomology of the site commutes with filtered colimits of abelian
sheaves of shape `I`, for every `p`. -/
public lemma isIso_colimit_post_rightDerived_globalSections_of_isIso_colimit_post_ext
    (S : Set (Sheaf J (Type u)))
    (h_terminal : ∃ K ∈ S, Sheaf.IsLocallySurjective (terminal.from K))
    (h_lift : ∀ {G K : Sheaf J (Type u)} (f : G ⟶ K), K ∈ S →
      Sheaf.IsLocallySurjective f →
        ∃ K' ∈ S, ∃ g : K' ⟶ G, Sheaf.IsLocallySurjective (g ≫ f))
    (h_product : ∀ K ∈ S, ∀ K' ∈ S,
      ∃ K'' ∈ S, ∃ f : K'' ⟶ K ⨯ K', Sheaf.IsLocallySurjective f)
    (h_quasiCompact : ∀ K ∈ S, Sheaf.IsQuasiCompact K)
    (hlocal : ∀ K ∈ S, ∀ (r q : ℕ), ∀ D : I ⥤ Sheaf J Ab.{u},
      IsIso (colimit.post D (Abelian.extFunctorObj.{u}
        ((Presheaf.freeAbelianSheaf J).obj (CoveringSet.sheafPower J K r).obj) q)))
    (p : ℕ) (F : I ⥤ Sheaf J Ab.{u}) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived p)) :=
  isIso_colimit_post_rightDerived_globalSections_of_acyclic J S h_terminal h_lift h_product
    h_quasiCompact
    (fun n G hG => isZero_rightDerived_globalSections_colimit_of_isIso J S h_terminal h_lift n G hG
      (fun K hK r q _ D => hlocal K hK r q D)) p F

end Stacks.Cohomology.ColimitsOfCohomology

end
