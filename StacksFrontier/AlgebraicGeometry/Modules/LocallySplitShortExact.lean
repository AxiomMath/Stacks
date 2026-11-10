module

public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A short exact sequence with finite locally free quotient splits locally

Let `X` be a scheme and let `0 → ℰ → ℱ → 𝒢 → 0` be a short exact sequence of `𝒪_X`-modules
with `𝒢` finite locally free. Then every point of `X` has an open neighbourhood `U` over which
the sequence splits: the restricted sequence carries a `CategoryTheory.ShortComplex.Splitting`,
that is, a section `𝒢|_U ⟶ ℱ|_U` of the surjection together with the retraction
`ℱ|_U ⟶ ℰ|_U` it determines. Only a *local* splitting can be expected, because the lift of a
section of `𝒢` through the surjection exists only locally.

The argument is the standard one. Near a point `𝒢` is free on a finite index set, so it has
finitely many sections over an open `V` forming a basis; the surjection `ℱ ⟶ 𝒢` is surjective on
stalks, so each of those sections lifts over a neighbourhood of the point, and the finitely many
neighbourhoods obtained can be intersected. Over the resulting open `U` the universal property of
the free module turns the lifted sections into a morphism `𝒢|_U ⟶ ℱ|_U` splitting the surjection,
and the retraction comes for free from
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection`, since restriction along an open
immersion is exact.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardRestrictSections`: a section of a module over an
  open `U` read as a global section of the pushforward of its restriction to `U`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_sections_lift`: a finite family of sections of a
  quotient module lifts over a neighbourhood of any point.
* `AlgebraicGeometry.Scheme.Modules.shortExact_map_restrictFunctor`: restriction of modules along
  an open immersion preserves short exactness.
* `AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict_of_iso_free`: a short exact
  sequence whose quotient is free of finite rank splits over an open neighbourhood of every point.
* `AlgebraicGeometry.Scheme.Modules.nonempty_splitting_restrict_opensRange`: a short complex which
  splits after restriction along an open immersion splits after restriction to the image open.
* `AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict` and
  `AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree`:
  **a short exact sequence of `𝒪_X`-modules whose quotient is finite locally free splits over an
  open neighbourhood of every point**, with the local freeness of the quotient given pointwise
  and as a class respectively.

## Implementation notes

The lifted sections are assembled into a morphism out of the free module not over the open
subscheme `U` but over `X`, through the adjunction
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction` between restriction and pushforward: a
morphism `(free I)|_U ⟶ ℱ|_U` is a morphism `free I ⟶ (U.ι)_*(ℱ|_U)`, and the latter is a family
of global sections of `(U.ι)_*(ℱ|_U)`, i.e. of sections of `ℱ` over the opens `U ⊓ V`. Phrased
this way the equation to be checked compares two families of *global* sections of `𝒢`, so the
trivialisation of `𝒢` never has to be transported to a smaller open; the unit of the adjunction
is restriction of sections, which
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app` computes definitionally.

Restriction to an open is spelled `AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, the
form with the best definitional behaviour: `Γ(M.restrict f, W)` is `Γ(M, f ''ᵁ W)` by `rfl`.
Restricting to an open of an open subscheme produces a restriction along the composite open
immersion rather than along the inclusion of an open of `X`; the two are compared through
`AlgebraicGeometry.Scheme.Hom.isoOpensRange`, by transporting the splitting along an isomorphism
of restriction functors rather than by transporting the trivialisation.

The germ lemmas are stated for presheaves of abelian groups on a topological space because the
underlying presheaf of a sheaf of modules is one, and because the intersection of finitely many
opens is where the finiteness of the rank is used:
`TopologicalSpace.Opens.coe_iInf` needs a finite index type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-! ### Germs of finite families of sections -/

/-- Finitely many opens containing a point have an intersection with `V` which is an open
neighbourhood of that point. -/
private theorem exists_le_inf_family {Y : TopCat.{u}} {I : Type*} [Finite I] (x : ↥Y)
    {V : TopologicalSpace.Opens ↥Y} (hxV : x ∈ V) {W : I → TopologicalSpace.Opens ↥Y}
    (hW : ∀ i, x ∈ W i) :
    ∃ (U : TopologicalSpace.Opens ↥Y) (_ : U ≤ V) (_ : x ∈ U), ∀ i, U ≤ W i :=
  ⟨V ⊓ ⨅ i, W i, inf_le_left, ⟨hxV, (Opens.coe_iInf W) ▸ Set.mem_iInter.mpr hW⟩,
    fun i => inf_le_right.trans (iInf_le W i)⟩

/-- Finitely many elements of a stalk are simultaneously germs of sections over one open
neighbourhood of the point contained in a prescribed one. -/
private theorem exists_germ_eq_family {Y : TopCat.{u}} (G : TopCat.Presheaf Ab.{u} Y)
    {I : Type*} [Finite I] (x : ↥Y) (m : I → ToType (G.stalk x))
    {V : TopologicalSpace.Opens ↥Y} (hxV : x ∈ V) :
    ∃ (U : TopologicalSpace.Opens ↥Y) (_ : U ≤ V) (hxU : x ∈ U)
      (s : I → ToType (G.obj (op U))), ∀ i, (G.germ U x hxU).hom (s i) = m i := by
  choose W hWV hW s hs using fun i => TopCat.Presheaf.exists_le_germ_eq G (m i) hxV
  obtain ⟨U, hUV, hx, hle⟩ := exists_le_inf_family x hxV hW
  exact ⟨U, hUV, hx, fun i => (G.map (homOfLE (hle i)).op).hom (s i),
    fun i => (TopCat.Presheaf.germ_res_apply G (homOfLE (hle i)) x hx (s i)).trans (hs i)⟩

/-- Finitely many pairs of sections over an open with equal germs at a point agree over one open
neighbourhood of that point. -/
private theorem exists_le_res_eq_of_germ_eq {Y : TopCat.{u}} (G : TopCat.Presheaf Ab.{u} Y)
    {I : Type*} [Finite I] {V : TopologicalSpace.Opens ↥Y} (x : ↥Y) (hxV : x ∈ V)
    (s t : I → ToType (G.obj (op V)))
    (h : ∀ i, (G.germ V x hxV).hom (s i) = (G.germ V x hxV).hom (t i)) :
    ∃ (U : TopologicalSpace.Opens ↥Y) (hUV : U ≤ V) (_ : x ∈ U),
      ∀ i, (G.map (homOfLE hUV).op).hom (s i) = (G.map (homOfLE hUV).op).hom (t i) := by
  choose W hW iU iV hst using fun i => TopCat.Presheaf.germ_eq G x hxV hxV (s i) (t i) (h i)
  obtain ⟨U, hUV, hx, hle⟩ := exists_le_inf_family x hxV hW
  refine ⟨U, hUV, hx, fun i => ?_⟩
  have hWV (i : I) : W i ≤ V := leOfHom (iU i)
  have hst' (i : I) : (G.map (homOfLE (hWV i)).op).hom (s i)
      = (G.map (homOfLE (hWV i)).op).hom (t i) := by
    rw [show homOfLE (hWV i) = iU i from Subsingleton.elim _ _]
    exact (hst i).trans (congrArg (fun q : W i ⟶ V => (G.map q.op).hom (t i))
      (Subsingleton.elim (iV i) (iU i)))
  calc (G.map (homOfLE hUV).op).hom (s i)
      = (G.map (homOfLE (hle i)).op).hom ((G.map (homOfLE (hWV i)).op).hom (s i)) :=
        (TopCat.Presheaf.restrict_restrict (hle i) (hWV i) (s i)).symm
    _ = (G.map (homOfLE (hle i)).op).hom ((G.map (homOfLE (hWV i)).op).hom (t i)) :=
        congrArg _ (hst' i)
    _ = (G.map (homOfLE hUV).op).hom (t i) :=
        TopCat.Presheaf.restrict_restrict (hle i) (hWV i) (t i)

variable {X : Scheme.{u}}

/-! ### Lifting sections through an epimorphism -/

/-- **A finite family of sections of a quotient lifts over a neighbourhood of any point.**
For an epimorphism `g : M ⟶ N` of `𝒪_X`-modules, finitely many sections of `N` over an open `V`
and a point `x` of `V`, there is an open neighbourhood `U ≤ V` of `x` over which each of them is
the image of a section of `M`. -/
theorem exists_sections_lift {M N : X.Modules} (g : M ⟶ N) (hg : Epi g)
    {I : Type*} [Finite I] (x : X) {V : X.Opens} (hxV : x ∈ V) (t : I → Γ(N, V)) :
    ∃ (U : X.Opens) (hUV : U ≤ V) (_ : x ∈ U) (b : I → Γ(M, U)),
      ∀ i, (g.val.app (op U)).hom (b i) = (N.presheaf.map (homOfLE hUV).op).hom (t i) := by
  classical
  have hsurj := (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := X.ringCatSheaf) g).1 hg x
  choose m hm using fun i : I =>
    hsurj ((TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf V x hxV).hom (t i))
  obtain ⟨U₁, hU₁V, hxU₁, c, hc⟩ := exists_germ_eq_family M.val.presheaf x m hxV
  have hgerm (i : I) :
      (TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf U₁ x hxU₁).hom
          ((g.val.app (op U₁)).hom (c i))
        = (TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf U₁ x hxU₁).hom
          ((N.presheaf.map (homOfLE hU₁V).op).hom (t i)) := by
    rw [← AlgebraicGeometry.SheafOfModules.stalkMap_germ X.ringCatSheaf x g U₁ hxU₁ (c i),
      hc i, hm i]
    exact (TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE hU₁V) x hxU₁ (t i)).symm
  obtain ⟨U, hUU₁, hxU, hres⟩ :=
    exists_le_res_eq_of_germ_eq N.val.presheaf x hxU₁
      (fun i => (g.val.app (op U₁)).hom (c i))
      (fun i => (N.presheaf.map (homOfLE hU₁V).op).hom (t i)) hgerm
  refine ⟨U, hUU₁.trans hU₁V, hxU,
    fun i => (M.presheaf.map (homOfLE hUU₁).op).hom (c i), fun i => ?_⟩
  exact (PresheafOfModules.naturality_apply g.val (homOfLE hUU₁).op (c i)).trans
    ((hres i).trans (TopCat.Presheaf.restrict_restrict (F := N.val.presheaf) hUU₁ hU₁V (t i)))

/-! ### Sections of the pushforward of a restriction -/

/-- A section of `M` over an open `U`, as a global section of the pushforward of the restriction
of `M` to `U`: over an open `V` its value is the restriction of the given section to `U ⊓ V`. -/
def pushforwardRestrictSections (M : X.Modules) (U : X.Opens) (b : Γ(M, U)) :
    ((pushforward U.ι).obj (M.restrict U.ι)).sections :=
  PresheafOfModules.sectionsMk
    (fun V => (M.presheaf.map (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ V.unop))).op).hom b)
    (fun {V V'} f => by
      have h : U.ι ''ᵁ (U.ι ⁻¹ᵁ V'.unop) ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop) :=
        leOfHom (U.ι.opensFunctor.map ((Opens.map U.ι.base).map f.unop))
      have hmap : ∀ z : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop)),
          (ConcreteCategory.hom (((pushforward U.ι).obj (M.restrict U.ι)).val.map f)) z
            = (M.presheaf.map (homOfLE h).op).hom z := fun _ => rfl
      rw [hmap]
      exact TopCat.Presheaf.restrict_restrict (F := M.presheaf) h (U.ι_image_le _) b)

/-- The value of `pushforwardRestrictSections M U b` over an open `V` is the restriction of the
section `b` to `U ⊓ V`. -/
@[simp]
theorem pushforwardRestrictSections_val (M : X.Modules) (U : X.Opens) (b : Γ(M, U))
    (V : X.Opens) :
    (pushforwardRestrictSections M U b).val (op V)
      = (M.presheaf.map (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ V))).op).hom b :=
  rfl

/-! ### Restriction along an open immersion is exact -/

/-- **Restriction of modules along an open immersion preserves short exactness.** Restriction
preserves finite limits, hence monomorphisms and exactness, and is a left adjoint, hence
preserves epimorphisms. -/
theorem shortExact_map_restrictFunctor {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (restrictFunctor j)).ShortExact := by
  have hcol : PreservesColimitsOfSize.{u, u} (restrictFunctor j) :=
    (Adjunction.ofIsLeftAdjoint (restrictFunctor j)).leftAdjoint_preservesColimits
  have hlim := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (restrictFunctor j)).1 inferInstance S hS
  have hepi := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (restrictFunctor j)).1 inferInstance S hS
  exact { exact := hlim.1, mono_f := hlim.2, epi_g := hepi.2 }

/-! ### The local splitting -/

/-- **A short exact sequence of `𝒪_X`-modules whose quotient is free of finite rank splits over
an open neighbourhood of every point.** A basis of global sections of the quotient lifts through
the surjection over a neighbourhood `U` of the point, and the lifts assemble into a section of
the restricted surjection. -/
theorem exists_nonempty_splitting_restrict_of_iso_free (S : ShortComplex X.Modules)
    (hS : S.ShortExact) {I : Type u} [Finite I]
    (e : S.X₃ ≅ SheafOfModules.free I) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (S.map (restrictFunctor U.ι)).Splitting := by
  classical
  obtain ⟨U, hUtop, hxU, b, hb⟩ := exists_sections_lift S.g hS.epi_g x
    (V := (⊤ : X.Opens)) (Opens.mem_top x) (fun i => (S.X₃.freeHomEquiv e.inv i).val (op ⊤))
  refine ⟨U, hxU, ?_⟩
  have hbU (i : I) : (S.g.val.app (op U)).hom (b i)
      = (S.X₃.freeHomEquiv e.inv i).val (op U) :=
    (hb i).trans ((S.X₃.freeHomEquiv e.inv i).property (homOfLE hUtop).op)
  set F := restrictFunctor U.ι
  set adj := restrictAdjunction U.ι
  set h : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ (pushforward U.ι).obj (F.obj S.X₂) :=
    ((pushforward U.ι).obj (F.obj S.X₂)).freeHomEquiv.symm
      (fun i => pushforwardRestrictSections S.X₂ U (b i)) with hhdef
  set σ : F.obj (SheafOfModules.free (R := X.ringCatSheaf) I) ⟶ F.obj S.X₂ :=
    (adj.homEquiv _ (F.obj S.X₂)).symm h with hσdef
  have key : σ ≫ F.map S.g = F.map e.inv := by
    refine (adj.homEquiv _ (F.obj S.X₃)).injective ?_
    refine (adj.homEquiv_naturality_right σ (F.map S.g)).trans ?_
    refine Eq.trans (congrArg (fun z => z ≫ (pushforward U.ι).map (F.map S.g))
      ((adj.homEquiv _ (F.obj S.X₂)).apply_symm_apply h)) ?_
    refine Eq.trans ?_ (adj.homEquiv_unit _ _ (F.map e.inv)).symm
    refine Eq.trans ?_ (adj.unit.naturality e.inv)
    refine ((pushforward U.ι).obj (F.obj S.X₃)).freeHomEquiv.injective (funext fun i => ?_)
    have hA : ((pushforward U.ι).obj (F.obj S.X₂)).freeHomEquiv h i
        = pushforwardRestrictSections S.X₂ U (b i) := by
      rw [hhdef]
      exact congrFun (((pushforward U.ι).obj (F.obj S.X₂)).freeHomEquiv.apply_symm_apply _) i
    change SheafOfModules.sectionsMap ((pushforward U.ι).map (F.map S.g))
          (((pushforward U.ι).obj (F.obj S.X₂)).freeHomEquiv h i)
        = SheafOfModules.sectionsMap (adj.unit.app S.X₃) (S.X₃.freeHomEquiv e.inv i)
    rw [hA]
    refine PresheafOfModules.sections_ext _ _ fun V => ?_
    have hL : ∀ z : Γ(S.X₂, U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop)),
        (ConcreteCategory.hom (((pushforward U.ι).map (F.map S.g)).val.app V)) z
          = (S.g.val.app (op (U.ι ''ᵁ (U.ι ⁻¹ᵁ V.unop)))).hom z := fun _ => rfl
    have hR : ∀ z : Γ(S.X₃, V.unop),
        (ConcreteCategory.hom ((adj.unit.app S.X₃).val.app V)) z
          = (S.X₃.presheaf.map
              (homOfLE (U.ι.image_preimage_le V.unop)).op).hom z := fun _ => rfl
    change (ConcreteCategory.hom (((pushforward U.ι).map (F.map S.g)).val.app V))
        ((pushforwardRestrictSections S.X₂ U (b i)).val V)
          = (ConcreteCategory.hom ((adj.unit.app S.X₃).val.app V))
            ((S.X₃.freeHomEquiv e.inv i).val V)
    refine (hL _).trans (Eq.trans ?_ (hR _).symm)
    refine (PresheafOfModules.naturality_apply S.g.val
      (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ V.unop))).op (b i)).trans ?_
    refine Eq.trans (congrArg _ (hbU i)) ?_
    exact ((S.X₃.freeHomEquiv e.inv i).property
        (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ V.unop))).op).trans
      ((S.X₃.freeHomEquiv e.inv i).property
        (homOfLE (U.ι.image_preimage_le V.unop)).op).symm
  obtain ⟨hex, hmono⟩ := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).1
    inferInstance S hS
  refine ⟨ShortComplex.Splitting.ofExactOfSection (S.map F) hex (F.map e.hom ≫ σ) ?_ hmono⟩
  change (F.map e.hom ≫ σ) ≫ F.map S.g = 𝟙 _
  rw [Category.assoc, key]
  exact (F.mapIso e).hom_inv_id

/-! ### Transport along an open immersion -/

/-- **A short complex which splits after restriction along an open immersion splits after
restriction to the image open.** The open immersion factors as an isomorphism onto the image open
followed by its inclusion, and restriction along an isomorphism carries the splitting across. -/
theorem nonempty_splitting_restrict_opensRange {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (S : ShortComplex X.Modules)
    (hj : Nonempty (S.map (restrictFunctor j)).Splitting) :
    Nonempty (S.map (restrictFunctor j.opensRange.ι)).Splitting := by
  obtain ⟨sp⟩ := hj
  exact ⟨(sp.map (restrictFunctor j.isoOpensRange.inv)).ofIso
    (S.mapNatIso ((restrictFunctorCongr j.isoOpensRange_inv_comp).symm ≪≫
      restrictFunctorComp j.isoOpensRange.inv j)).symm⟩

/-- **A finite locally free quotient makes a short exact sequence of `𝒪_X`-modules split over an
open neighbourhood of every point.** Over such an open the restricted sequence has a splitting,
whose section splits the surjection and whose retraction splits the injection. -/
@[ega "0 5.4.9" "special case"]
theorem exists_nonempty_splitting_restrict (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hX₃ : IsFiniteLocallyFree S.X₃) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (S.map (restrictFunctor U.ι)).Splitting := by
  obtain ⟨V, hxV, I, hI, ⟨e⟩⟩ := hX₃ x
  have := hI
  obtain ⟨W, hxW, hsp⟩ := exists_nonempty_splitting_restrict_of_iso_free
    (S.map (restrictFunctor V.ι)) (shortExact_map_restrictFunctor V.ι S hS) e ⟨x, hxV⟩
  obtain ⟨sp⟩ := hsp
  have hsp' : Nonempty (S.map (restrictFunctor (W.ι ≫ V.ι))).Splitting :=
    ⟨sp.ofIso (S.mapNatIso (restrictFunctorComp W.ι V.ι)).symm⟩
  refine ⟨(W.ι ≫ V.ι).opensRange, ?_,
    nonempty_splitting_restrict_opensRange (W.ι ≫ V.ι) S hsp'⟩
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
  exact ⟨⟨x, hxV⟩, hxW, rfl⟩

/-- **A finite locally free quotient makes a short exact sequence of `𝒪_X`-modules split over an
open neighbourhood of every point**, with the finite local freeness of the quotient supplied as
the class of [Stacks, Tag 01C6]. -/
@[ega "0 5.4.9" "special case"]
theorem exists_nonempty_splitting_restrict_of_isFiniteLocallyFree (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    [hX₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₃] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (S.map (restrictFunctor U.ι)).Splitting :=
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.mk
      (M := S.X₃) hX₃.exists_isFiniteLocallyFreeData
  exists_nonempty_splitting_restrict S hS
    (isFiniteLocallyFree_of_isFiniteLocallyFree S.X₃) x

end AlgebraicGeometry.Scheme.Modules

end
