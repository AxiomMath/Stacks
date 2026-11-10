module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AnnihilationLocality

/-!
# The annihilation of [Stacks, Tag 07Q9] from sections over a basis

The conclusion `...SmallSite.Annihilation07Q9` of [Stacks, Tag 07Q9] is that `q • 𝟙` vanishes on
every cohomology sheaf of a cone of a morphism of `D⁺(Ab(X_Zar))`.  The proof in the source
computes the cone on sections over the opens of a basis of `X` (the affine opens over which `f` is
a tower of `α_p`-covers) and concludes that `q` kills the cohomology of the *presheaf* of
sections there.  This module turns that sectionwise statement into the sheaf statement.

## The argument

Cohomology sheaves are the sheafifications of presheaf cohomology, and a presheaf whose sections
over a basis are killed by `q` has its sheafification killed by `q`.  We do not pass through the
sheafification: for a complex `K` of abelian sheaves, the cycles sheaf `Z^j(K)` is computed
sectionwise (kernels of sheaves are kernels of presheaves), so a section `z` of `Z^j(K)` over `V`
restricts, over each basic open `W ⊆ V`, to a cycle of the complex of abelian groups `K(W)`.  If
`q` kills `H^j(K(W))`, then `q • z|_W` is a boundary, so its image in the cohomology sheaf
`H^j(K)` vanishes on `W`; by the sheaf axiom that image vanishes on `V`.  Hence
`q • (Z^j(K) ⟶ H^j(K)) = 0`, and since this map is an epimorphism, `q • 𝟙 (H^j(K)) = 0`.

## Main results

* `Stacks.Triangulated.exists_f_eq_smul_of_smul_id_homology_eq_zero` — in a short complex of
  abelian groups whose homology is killed by `q`, `q` times a cycle is a boundary.
* `Stacks.Triangulated.coneHomologyAnnihilation_of_arrowIso` — in any `D⁺(𝒜)`, the conclusion of
  [Stacks, Tag 07Q9] for `α` follows from `q` killing the homology of the mapping cone of a chain
  map `φ` whose image in `D(𝒜)` is isomorphic, as an arrow, to the image of `α`.
* `...SmallSite.smul_id_homology_eq_zero_of_isBasis` — **the chain-level basis lemma**: if `q`
  kills `H^j` of the complex of sections over every open of a basis, it kills the cohomology sheaf
  `H^j(K)`.
* `...SmallSite.sectionsMappingConeIso` — the sections over an open of a mapping cone are the
  mapping cone of the sections.
* `...SmallSite.annihilation07Q9_of_isBasis_mappingCone` — **the derived-category reading**:
  `Annihilation07Q9 S q α` follows from `q` killing the cohomology of the mapping cone of the
  sections of a chain-level model `φ` of `α`, over every open of a basis.

## No tag is placed

**No `@[stacks]` attribute is placed.**  These are the sheaf-theoretic reductions of
[Stacks, Tag 07Q9]; the sectionwise annihilation they consume is a hypothesis.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)

Tags covered: none.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w u

noncomputable section

namespace Stacks.Triangulated

/-- **In a short complex of abelian groups whose homology is killed by `q`, `q` times a cycle is
a boundary.**  The homology is the quotient of the cycles `ker g` by the image of `f`, by
`CategoryTheory.ShortComplex.abHomologyIso`, and `q • 𝟙` vanishing on it says that `q • x` lies in
that image for every cycle `x`. -/
theorem exists_f_eq_smul_of_smul_id_homology_eq_zero (T : ShortComplex AddCommGrpCat.{u})
    (q : ℤ) (h : q • 𝟙 T.homology = 0) (x : T.X₂) (hx : T.g x = 0) :
    ∃ y : T.X₁, T.f y = q • x := by
  have h' : q • 𝟙 (AddCommGrpCat.of
      ((AddMonoidHom.ker T.g.hom) ⧸ AddMonoidHom.range T.abToCycles)) = 0 :=
    Stacks.Algebraization.smul_id_eq_zero_of_iso q T.abHomologyIso.symm h
  have h2 := ConcreteCategory.congr_hom h'
    (QuotientAddGroup.mk' (AddMonoidHom.range T.abToCycles) ⟨x, hx⟩)
  simp only [AddCommGrpCat.hom_zsmul, AddCommGrpCat.hom_id, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] at h2
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h2
  obtain ⟨y, hy⟩ := h2
  exact ⟨y, congrArg Subtype.val hy⟩

variable (𝒜 : Type*) [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **The conclusion of [Stacks, Tag 07Q9] from a chain-level model.**  Let `α : A ⟶ B` be a
morphism of `D⁺(𝒜)` and `φ : K ⟶ L` a chain map of `ℤ`-indexed complexes whose image in `D(𝒜)` is
isomorphic, as an arrow, to the image of `α`.  If `q` kills every homology object of the mapping
cone of `φ`, then `q` kills the cohomology objects of every cone of `α`.

A distinguished triangle on `α` is sent by `DerivedCategory.Plus.ι` to a distinguished triangle
of `D(𝒜)` whose first two terms are those of the mapping cone triangle of `φ`, so the two are
isomorphic by `CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂`; the cohomology of the third
term of the latter is the homology of the mapping cone, by
`DerivedCategory.homologyFunctorFactors`. -/
theorem coneHomologyAnnihilation_of_arrowIso (q : ℕ) {A B : DerivedCategory.Plus 𝒜}
    (α : A ⟶ B) {K L : CochainComplex 𝒜 ℤ} (φ : K ⟶ L)
    (e : Arrow.mk (DerivedCategory.Plus.ι.map α) ≅ Arrow.mk (DerivedCategory.Q.map φ))
    (h : ∀ j : ℤ, (q : ℤ) • 𝟙 ((CochainComplex.mappingCone φ).homology j) = 0) :
    ConeHomologyAnnihilation 𝒜 q α := by
  intro E v wE hT j
  have iso := isoTriangleOfIso₁₂ _ _ (DerivedCategory.Plus.ι.map_distinguished _ hT)
    (DerivedCategory.mappingCone_triangle_distinguished φ)
    (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) (Arrow.w e.hom).symm
  exact Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
    ((DerivedCategory.homologyFunctor 𝒜 j).mapIso (Triangle.π₃.mapIso iso) ≪≫
      (DerivedCategory.homologyFunctorFactors 𝒜 j).app _) (h j)

end Stacks.Triangulated

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **A cycle over an open where the sections have `q`-torsion cohomology becomes zero in the
cohomology sheaf after multiplication by `q`.**  Let `K` be a complex of abelian sheaves on
`X_Zar` and `W` an open of `X` such that `q` kills `H^j(K(W))`.  For a section `z` over `W` of
the cycles sheaf `Z^j(K)`, its image in `K^j(W)` is a cycle of `K(W)`, so `q` times it is a
boundary `d y`; then `q • z` is the image of `y` under `K^{j-1} ⟶ Z^j(K)` (the map
`Z^j(K) ⟶ K^j` being injective on sections), and so it dies in `H^j(K)`. -/
theorem homologyπ_app_zsmul_eq_zero
    (K : CochainComplex (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ℤ) (j q : ℤ)
    (W : S.X.Opens)
    (hW : q • 𝟙 (((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex _).obj K).homology j) = 0)
    (z : ToType ((K.sc j).cycles.obj.obj (op W))) :
    (K.sc j).homologyπ.hom.app (op W) (q • z) = 0 := by
  have hmono : Function.Injective ((K.sc j).iCycles.hom.app (op W)) := by
    have : Mono (K.sc j).iCycles.hom := (sheafToPresheaf _ _).map_mono (K.sc j).iCycles
    exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hx : (((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex _).obj K).sc j).g
      ((K.sc j).iCycles.hom.app (op W) z) = 0 := by
    change ((K.sc j).iCycles ≫ (K.sc j).g).hom.app (op W) z = 0
    rw [(K.sc j).iCycles_g]
    rfl
  obtain ⟨y, hy⟩ := Stacks.Triangulated.exists_f_eq_smul_of_smul_id_homology_eq_zero _ q hW _ hx
  have hyz : (K.sc j).toCycles.hom.app (op W) y = q • z := by
    apply hmono
    refine Eq.trans ?_ (hy.trans (map_zsmul _ q z).symm)
    change ((K.sc j).toCycles ≫ (K.sc j).iCycles).hom.app (op W) y = _
    rw [(K.sc j).toCycles_i]
    rfl
  rw [← hyz]
  change ((K.sc j).toCycles ≫ (K.sc j).homologyπ).hom.app (op W) y = 0
  rw [(K.sc j).toCycles_comp_homologyπ]
  rfl

/-- **The chain-level basis lemma.**  Let `K` be a complex of abelian sheaves on `X_Zar` and `ℬ`
a basis of the topology of `X`.  If `q` kills `H^j` of the complex of abelian groups of sections
of `K` over every member of `ℬ`, then `q` kills the cohomology sheaf `H^j(K)`.

This is the statement that a presheaf whose sections over a basis are killed by `q` has
`q`-torsion sheafification, read on the presheaf cohomology of `K`.  The proof shows that
`q • (Z^j(K) ⟶ H^j(K))` vanishes on every section, by `homologyπ_app_zsmul_eq_zero` over the
basic opens inside a given open and `TopCat.Sheaf.eq_of_locally_eq'`, and cancels the epimorphism
`Z^j(K) ⟶ H^j(K)`. -/
theorem smul_id_homology_eq_zero_of_isBasis
    (K : CochainComplex (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ℤ) (j q : ℤ)
    {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, q • 𝟙 (((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
      (op W)).mapHomologicalComplex _).obj K).homology j) = 0) :
    q • 𝟙 (K.homology j) = 0 := by
  have hπ : q • (K.sc j).homologyπ = 0 := by
    refine Sheaf.hom_ext ?_
    ext V z
    change AddCommGrpCat.Hom.hom (q • (K.sc j).homologyπ.hom.app V) z = 0
    rw [AddCommGrpCat.hom_zsmul, AddMonoidHom.smul_apply, ← map_zsmul]
    refine TopCat.Sheaf.eq_of_locally_eq' (F := (K.sc j).homology)
      (fun i : {W : S.X.Opens // W ∈ ℬ ∧ W ≤ V.unop} => i.1) V.unop
      (fun i => homOfLE i.2.2) ?_ _ 0 fun i => ?_
    · intro x hx
      obtain ⟨U', hU'ℬ, hxU', hU'V⟩ := (Opens.isBasis_iff_nbhd.1 hℬ) hx
      exact Opens.mem_iSup.2 ⟨⟨U', hU'ℬ, hU'V⟩, hxU'⟩
    · rw [map_zero, ← NatTrans.naturality_apply, map_zsmul]
      exact homologyπ_app_zsmul_eq_zero S K j q i.1 (h i.1 i.2.1) _
  change q • 𝟙 (K.sc j).homology = 0
  rw [← cancel_epi (K.sc j).homologyπ, comp_zero, Preadditive.comp_zsmul, Category.comp_id]
  exact hπ

/-- **The sections over an open of a mapping cone are the mapping cone of the sections.**  The
sections functor at `W` is additive, so this is
`CochainComplex.mappingCone.mapHomologicalComplexIso`. -/
def sectionsMappingConeIso
    {K L : CochainComplex (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (φ : K ⟶ L) (W : S.X.Opens) :
    (((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex
      _).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ((((sheafSections (opensTopology S)
        AddCommGrpCat.{u + 1}).obj (op W)).mapHomologicalComplex _).map φ) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso φ _

/-- **The conclusion of [Stacks, Tag 07Q9] from sections over a basis.**  Let `α : A ⟶ B` be a
morphism of `D⁺(Ab(X_Zar))` modelled by a chain map `φ : K ⟶ L` of complexes of abelian sheaves,
in the sense that the images of `α` and `φ` in `D(Ab(X_Zar))` are isomorphic arrows, and let `ℬ`
be a basis of the topology of `X`.  If, over every `W ∈ ℬ`, `q` kills the cohomology of the
mapping cone of the chain map of abelian groups `φ(W) : K(W) ⟶ L(W)`, then
`Annihilation07Q9 S q α` holds.

The sectionwise hypothesis is moved onto the sections of the mapping cone of `φ` by
`sectionsMappingConeIso`, turned into the annihilation of the cohomology sheaves of that cone by
`smul_id_homology_eq_zero_of_isBasis`, and transported to every cone of `α` by
`Stacks.Triangulated.coneHomologyAnnihilation_of_arrowIso`. -/
theorem annihilation07Q9_of_isBasis_mappingCone
    [HasDerivedCategory.{w} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (α : A ⟶ B)
    {K L : CochainComplex (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ℤ} (φ : K ⟶ L)
    (e : Arrow.mk (DerivedCategory.Plus.ι.map α) ≅ Arrow.mk (DerivedCategory.Q.map φ))
    {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, ∀ j : ℤ, (q : ℤ) • 𝟙 ((CochainComplex.mappingCone
      ((((sheafSections (opensTopology S) AddCommGrpCat.{u + 1}).obj
        (op W)).mapHomologicalComplex _).map φ)).homology j) = 0) :
    Annihilation07Q9 S q α :=
  Stacks.Triangulated.coneHomologyAnnihilation_of_arrowIso _ q α φ e fun j =>
    smul_id_homology_eq_zero_of_isBasis S _ j (q : ℤ) hℬ fun W hW =>
      Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ)
        (HomologicalComplex.homologyMapIso (sectionsMappingConeIso S φ W) j) (h W hW j)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
