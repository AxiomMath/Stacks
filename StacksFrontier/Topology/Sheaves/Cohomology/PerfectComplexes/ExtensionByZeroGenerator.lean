module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.UnitComplexMaps
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# A generator of the extension by zero of the structure sheaf

For an open `V` of a space `T` with a sheaf of rings `O`, the extension by zero `j_{V!} O_V`
of the structure sheaf of `V` is generated over `V` by a section `extGen O V`: every section over
an open `Z ⊆ V` is uniquely a multiple of its restriction, and a morphism `j_{V!} O_V ⟶ M` is
determined by the image of the generator, a section of `M` over `V`.

## Main definitions

* `extUnit`: The extension by zero `j_{V!} O_V`.
* `extGen`: The generator of `j_{V!} O_V` over `V`.
* `homOfSection`: The morphism `j_{V!} O_V ⟶ M` sending the generator to a section of `M`.

## Main results

* `homOfSection_extGen`: `homOfSection O V s` sends the generator to `s`.
* `exists_eq_smul_res_extGen`: Over `Z ⊆ V`, every section is a multiple of the generator.
* `eq_zero_of_smul_res_extGen`: Over `Z ⊆ V`, a multiple `c` of the generator vanishes only if
  `c = 0`.
* `exists_resS_eq_zero_of_not_mem`: A section of `j_{V!} O_V` vanishes near every point outside
  `V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.LeftDualPerfect

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- The extension by zero `j_{V!} O_V` of the structure sheaf of an open `V`. -/
abbrev extUnit (V : Opens T) : SheafOfModules.{u} O :=
  (jShriek V O).obj (SheafOfModules.unit (resRing V O))

/-- The open `V`, as the image of the whole of the open subspace `V`. -/
abbrev imTop (V : Opens T) : Opens T := (TopCat.Presheaf.imF V).obj ⊤

/-- The image of the whole of the open subspace `V` is `V`. -/
theorem imTop_eq (V : Opens T) : imTop V = V := by simp

/-- The generator of `j_{V!} O_V` over `V`: the image of `1` under the unit of `j_! ⊣ j^*`. -/
def extGen (V : Opens T) : (extUnit O V).val.obj (op (imTop V)) :=
  ((jShriekAdjunction V O).unit.app (SheafOfModules.unit (resRing V O))).val.app (op ⊤)
    (oneS (resRing V O))

/-- The morphism `j_{V!} O_V ⟶ M` sending the generator to a section of `M` over `V`. -/
def homOfSection {M : SheafOfModules.{u} O} (V : Opens T) (s : M.val.obj (op (imTop V))) :
    extUnit O V ⟶ M :=
  ((jShriekAdjunction V O).homEquiv _ _).symm (unitHomOfTop ((jStar V O).obj M) s)

/-- On an open `T'` of `V`, the restriction `φ|_V` of a morphism `φ` acts on sections as `φ` does
on the image of `T'`. -/
theorem jStar_map_app {M N : SheafOfModules.{u} O} (V : Opens T) (φ : M ⟶ N)
    (T' : Opens (Stacks.Topology.openSubspace V))
    (x : M.val.obj (op ((TopCat.Presheaf.imF V).obj T'))) :
    ((jStar V O).map φ).val.app (op T') x = φ.val.app (op ((TopCat.Presheaf.imF V).obj T')) x :=
  rfl

/-- The morphism `homOfSection O V s` sends the generator `extGen O V` to `s`. -/
theorem homOfSection_extGen {M : SheafOfModules.{u} O} (V : Opens T)
    (s : M.val.obj (op (imTop V))) :
    (homOfSection O V s).val.app (op (imTop V)) (extGen O V) = s := by
  have h : (jShriekAdjunction V O).homEquiv _ _ (homOfSection O V s) =
      unitHomOfTop ((jStar V O).obj M) s :=
    ((jShriekAdjunction V O).homEquiv _ _).apply_symm_apply _
  rw [Adjunction.homEquiv_unit] at h
  exact (congrArg (fun ψ => ψ.val.app (op ⊤) (oneS (resRing V O))) h).trans
    (unitHomOfTop_app_top ((jStar V O).obj M) s)

/-- Composing `homOfSection O V s` with `φ : M ⟶ N` gives the morphism attached to the section
`φ s`. -/
theorem homOfSection_comp {M N : SheafOfModules.{u} O} (V : Opens T)
    (s : M.val.obj (op (imTop V))) (φ : M ⟶ N) :
    homOfSection O V s ≫ φ = homOfSection O V (φ.val.app (op (imTop V)) s) := by
  have e1 : homOfSection O V s ≫ φ = ((jShriekAdjunction V O).homEquiv _ _).symm
      (unitHomOfTop ((jStar V O).obj M) s ≫ (jStar V O).map φ) :=
    (Adjunction.homEquiv_naturality_right_symm _ _ _).symm
  have e2 := unitHomOfTop_comp s ((jStar V O).map φ)
  exact e1.trans (congrArg (((jShriekAdjunction V O).homEquiv _ _).symm) e2)

/-- The unit `O_V ⟶ (j_{V!} O_V)|_V` of `j_! ⊣ j^*` at the structure sheaf. -/
abbrev extUnitIso (V : Opens T) :=
  (jShriekAdjunction V O).unit.app (SheafOfModules.unit (resRing V O))

/-- The unit `O_V ⟶ (j_{V!} O_V)|_V` is an isomorphism. -/
instance isIso_extUnitIso (V : Opens T) : IsIso (extUnitIso O V) := by
  have := isIso_jShriekAdjunction_unit V O
  infer_instance

/-- The generator of `j_{V!} O_V` over the image of an open of `V`. -/
def genAt (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V)) :
    (extUnit O V).val.obj (op ((TopCat.Presheaf.imF V).obj T')) :=
  (extUnitIso O V).val.app (op T') (1 : (resRing V O).obj.obj (op T'))

/-- On every open `T'` of `V`, the unit `O_V ⟶ (j_{V!} O_V)|_V` is bijective on sections. -/
theorem bijective_extUnitIso_app (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V)) :
    Function.Bijective ((extUnitIso O V).val.app (op T')) := by
  have : IsIso ((extUnitIso O V).val.app (op T')) :=
    (inferInstance : IsIso ((SheafOfModules.evaluation _ (op T')).map (extUnitIso O V)))
  exact ConcreteCategory.bijective_of_isIso _

/-- On an open `T'` of `V`, the unit `O_V ⟶ (j_{V!} O_V)|_V` sends a section `c` to
`c • genAt O V T'`. -/
theorem extUnitIso_app_eq_smul (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V))
    (c : O.obj.obj (op ((TopCat.Presheaf.imF V).obj T'))) :
    (extUnitIso O V).val.app (op T') c = c • genAt O V T' := by
  have h := ((extUnitIso O V).val.app (op T')).hom.map_smul c (1 : (resRing V O).obj.obj (op T'))
  exact (congrArg (fun z => (extUnitIso O V).val.app (op T') z) (mul_one c).symm).trans h

/-- Restriction of a section of a sheaf of modules over a sheaf of rings on a space. -/
abbrev resS {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} S)
    {V' V : Opens T} (h : V' ≤ V) (s : M.val.obj (op V)) : M.val.obj (op V') :=
  M.val.map (homOfLE h).op s

/-- The image of an open of `V` is contained in `V`. -/
theorem imF_le_imTop (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V)) :
    (TopCat.Presheaf.imF V).obj T' ≤ imTop V :=
  (TopCat.Presheaf.imF V).monotone le_top

/-- The generator `genAt O V T'` is the restriction of `extGen O V` to the image of `T'`. -/
theorem genAt_eq_res (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V)) :
    genAt O V T' = resS (extUnit O V) (imF_le_imTop V T') (extGen O V) := by
  have h := PresheafOfModules.naturality_apply (extUnitIso O V).val
    (homOfLE le_top : T' ⟶ ⊤).op (oneS (resRing V O))
  have h1 : (SheafOfModules.unit (resRing V O)).val.map (homOfLE le_top : T' ⟶ ⊤).op
      (oneS (resRing V O)) = (1 : (resRing V O).obj.obj (op T')) :=
    PresheafOfModules.unit_map_one _ _
  exact (congrArg (fun z => (extUnitIso O V).val.app (op T') z) h1.symm).trans h

/-- Every section of `j_{V!} O_V` over the image of an open `T'` of `V` is a multiple of
`genAt O V T'`. -/
theorem exists_eq_smul_genAt (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V))
    (σ : (extUnit O V).val.obj (op ((TopCat.Presheaf.imF V).obj T'))) :
    ∃ c : O.obj.obj (op ((TopCat.Presheaf.imF V).obj T')), σ = c • genAt O V T' := by
  obtain ⟨c, hc⟩ := (bijective_extUnitIso_app O V T').2 σ
  exact ⟨c, hc.symm.trans (extUnitIso_app_eq_smul O V T' c)⟩

/-- A multiple `c • genAt O V T'` vanishes only if `c = 0`. -/
theorem eq_zero_of_smul_genAt (V : Opens T) (T' : Opens (Stacks.Topology.openSubspace V))
    (c : O.obj.obj (op ((TopCat.Presheaf.imF V).obj T'))) (h : c • genAt O V T' = 0) : c = 0 :=
  (bijective_extUnitIso_app O V T').1
    ((extUnitIso_app_eq_smul O V T' c).trans (h.trans (map_zero _).symm))

/-- The morphism `homOfSection O V s` sends the restriction of `extGen O V` to that of `s`. -/
private theorem homOfSection_res_extGen {M : SheafOfModules.{u} O} (V : Opens T)
    (s : M.val.obj (op (imTop V))) {Z : Opens T} (hZ : Z ≤ imTop V) :
    (homOfSection O V s).val.app (op Z) (resS (extUnit O V) hZ (extGen O V)) = resS M hZ s := by
  rw [resS, PresheafOfModules.naturality_apply, homOfSection_extGen]

/-- The morphism `homOfSection O V s` sends `c • genAt O V T'` to `c` times the restriction
of `s`. -/
theorem homOfSection_genAt {M : SheafOfModules.{u} O} (V : Opens T)
    (s : M.val.obj (op (imTop V))) (T' : Opens (Stacks.Topology.openSubspace V))
    (c : O.obj.obj (op ((TopCat.Presheaf.imF V).obj T'))) :
    (homOfSection O V s).val.app (op ((TopCat.Presheaf.imF V).obj T')) (c • genAt O V T') =
      c • resS M (imF_le_imTop V T') s := by
  rw [map_smul, genAt_eq_res, homOfSection_res_extGen]

/-- Restricting twice is restricting once along the composite inclusion. -/
theorem resS_resS {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} S)
    {V'' V' V : Opens T} (h₁ : V'' ≤ V') (h₂ : V' ≤ V) (s : M.val.obj (op V)) :
    resS M h₁ (resS M h₂ s) = resS M (h₁.trans h₂) s := by
  rw [resS, resS, ← PresheafOfModules.map_comp_apply]
  rfl

/-- Restriction from an open to itself is the identity. -/
theorem resS_refl {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} S)
    {V : Opens T} (h : V ≤ V) (s : M.val.obj (op V)) : resS M h s = s := by
  rw [resS, show (homOfLE h).op = 𝟙 (op V) from rfl, PresheafOfModules.map_id]
  rfl

/-- Restriction is semilinear: `(c • s)|_{V'} = c|_{V'} • s|_{V'}`. -/
theorem resS_smul {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} S)
    {V' V : Opens T} (h : V' ≤ V) (c : S.obj.obj (op V)) (s : M.val.obj (op V)) :
    resS M h (c • s) = S.obj.map (homOfLE h).op c • resS M h s :=
  PresheafOfModules.map_smul _ _ _ _

/-- Restriction sends `0` to `0`. -/
theorem resS_zero {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} S)
    {V' V : Opens T} (h : V' ≤ V) : resS M h (0 : M.val.obj (op V)) = 0 :=
  map_zero _

/-- For an open `Z ⊆ V`, the morphism `homOfSection O V s` sends `c • extGen O V|_Z` to
`c • s|_Z`. -/
theorem homOfSection_smul_res_extGen {M : SheafOfModules.{u} O} (V : Opens T)
    (s : M.val.obj (op (imTop V))) {Z : Opens T} (hZ : Z ≤ imTop V) (c : O.obj.obj (op Z)) :
    (homOfSection O V s).val.app (op Z) (c • resS (extUnit O V) hZ (extGen O V)) =
      c • resS M hZ s := by
  rw [map_smul, homOfSection_res_extGen]

/-- An open `Z ⊆ V` is the image of its preimage in the open subspace `V`. -/
theorem imF_preimage_eq (V : Opens T) {Z : Opens T} (hZ : Z ≤ imTop V) :
    (TopCat.Presheaf.imF V).obj ((Opens.map (Opens.inclusion' V)).obj Z) = Z := by
  rw [TopologicalSpace.Opens.functor_obj_map_obj]
  exact inf_eq_right.mpr hZ

/-- For an open `Z ⊆ V`, every section of `j_{V!} O_V` over `Z` is a multiple of the restriction
of `extGen O V` to `Z`. -/
theorem exists_eq_smul_res_extGen (V : Opens T) {Z : Opens T} (hZ : Z ≤ imTop V)
    (σ : (extUnit O V).val.obj (op Z)) :
    ∃ c : O.obj.obj (op Z), σ = c • resS (extUnit O V) hZ (extGen O V) := by
  have e := imF_preimage_eq V hZ
  obtain ⟨c, hc⟩ := exists_eq_smul_genAt O V _ (resS (extUnit O V) e.le σ)
  refine ⟨O.obj.map (homOfLE e.ge).op c, ?_⟩
  have h2 := congrArg (resS (extUnit O V) e.ge) hc
  rwa [resS_resS, resS_refl, resS_smul, genAt_eq_res, resS_resS] at h2

/-- For an open `Z ⊆ V`, a multiple `c • extGen O V|_Z` vanishes only if `c = 0`. -/
theorem eq_zero_of_smul_res_extGen (V : Opens T) {Z : Opens T} (hZ : Z ≤ imTop V)
    (c : O.obj.obj (op Z)) (h : c • resS (extUnit O V) hZ (extGen O V) = 0) : c = 0 := by
  have e := imF_preimage_eq V hZ
  have h2 := congrArg (resS (extUnit O V) e.le) h
  rw [resS_smul, resS_resS, ← genAt_eq_res, resS_zero] at h2
  have h4 := congrArg (O.obj.map (homOfLE e.ge).op) (eq_zero_of_smul_genAt O V _ _ h2)
  simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using h4

/-- **A section of `j_{V!} O_V` vanishes near every point outside `V`.** -/
theorem exists_resS_eq_zero_of_not_mem (V : Opens T) {Z : Opens T}
    (σ : (extUnit O V).val.obj (op Z)) (y : T) (hy : y ∈ Z) (hyV : y ∉ V) :
    ∃ (Z' : Opens T) (h : Z' ≤ Z), y ∈ Z' ∧ resS (extUnit O V) h σ = 0 := by
  have hs : Subsingleton (ToType (TopCat.Presheaf.stalk (X := T) (extUnit O V).val.presheaf y)) :=
    AddCommGrpCat.isZero_iff_subsingleton.1
      (isZero_stalk_jShriek V O (SheafOfModules.unit (resRing V O)) y hyV)
  obtain ⟨Z', hyZ', i₁, i₂, e⟩ :=
    TopCat.Presheaf.germ_eq (X := T) (extUnit O V).val.presheaf y hy hy σ 0 (Subsingleton.elim _ _)
  refine ⟨Z', leOfHom i₁, hyZ', ?_⟩
  have e' : resS (extUnit O V) (leOfHom i₁) σ = resS (extUnit O V) (leOfHom i₂) 0 := e
  rw [e', resS_zero]

end Stacks.Cohomology.LeftDualPerfect
