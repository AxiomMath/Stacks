module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompJoin
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The sheaf `SheafHom_{𝒪_X}(M, N)` on the spaces-étale site

Let `X` be an algebraic space and `M`, `N` two `𝒪_X`-modules.  The rule sending an algebraic
space `φ : V ⟶ X` étale over `X` to the group `Hom_{𝒪_V}(φ^*M, φ^*N)` of morphisms of the
restrictions of `M` and `N` to `V`, with restriction along `V₂ ⟶ V` given by pullback of
morphisms read through the comparison of Stacks 03LU, is a sheaf on the spaces-étale site
`X_{spaces,étale}` of Stacks 03G0: the sheaf `SheafHom_{𝒪_X}(M, N)`.  No quasi-coherence is
assumed: the two modules are arbitrary.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModuleHom`: the presheaf `V ↦ Hom_{𝒪_V}(M|_V, N|_V)` on
  the spaces-étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_restrictForm_eq`: morphisms of restrictions along an
  étale covering whose restricted readings agree on the pairwise fibre products glue uniquely.
* `AlgebraicGeometry.Space.spacesEtaleModuleHom_map_eq`: the restriction maps of
  `spacesEtaleModuleHom` are the restricted readings of Stacks 03LU.
* `AlgebraicGeometry.Space.isSheaf_spacesEtaleModuleHom`: `spacesEtaleModuleHom` is a sheaf.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Conj

variable {X Y Z : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS Z.1 Z.2}

/-- Conjugating a morphism by the comparison `AlgebraicGeometry.Space.modulePullbackTriangle` is
its restricted reading of Stacks 03LU at the same factorization. -/
theorem conjHom_modulePullbackTriangle_eq_restrictForm {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (hk : f ≫ g = k)
    (θ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N) :
    Functor.conjHom (modulePullbackTriangle B S hS hk) θ =
      QuasiCoherentDescent.restrictForm B S hS f g k hk θ := by
  subst hk
  rw [modulePullbackTriangle_rfl, QuasiCoherentDescent.restrictForm_eq,
    QuasiCoherentDescent.factorForm_eq, QuasiCoherentDescent.pullbackComparison_rfl]
  rfl

end Conj

attribute [local irreducible] modulePullback smallEtaleRingedSite structureSheaf
  smallEtaleRingedToposHom chartFunctor comparisonFunctor

section Glue

variable {I : Type*} {X V : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS X.1 X.2}

/-- **The pairwise condition of Stacks 04W3 at one commuting square, from the agreement of the
readings.**  Let `p : P ⟶ Y`, `q : P ⟶ Y'` and `ψ : Y ⟶ V`, `ψ' : Y' ⟶ V` form a commuting
square over `φV : V ⟶ X`, and let `w`, `w'` be morphisms of the inverse images along `ψ`, `ψ'` of
`φV^*M` and `φV^*N`, read through Stacks 03LU as `x`, `x'` over `X`.  If the restricted readings
of `x` and `x'` to `P` agree, then `w` and `w'` are intertwined by the canonical comparison of
Stacks 04W5. -/
theorem canonicalComparison_naturality_of_restrictForm_factorForm_eq
    {P Y Y' : AlgebraicSpaces B S hS}
    (φV : V ⟶ X) (p : P ⟶ Y) (q : P ⟶ Y') (ψ : Y ⟶ V) (ψ' : Y' ⟶ V) (hpq : p ≫ ψ = q ≫ ψ')
    (φ : Y ⟶ X) (φ' : Y' ⟶ X) (hφ : ψ ≫ φV = φ) (hφ' : ψ' ≫ φV = φ')
    (hst : (p ≫ ψ) ≫ φV = p ≫ φ) (hsnd : q ≫ φ' = p ≫ φ)
    (w : (modulePullback B S hS ψ).obj ((modulePullback B S hS φV).obj M) ⟶
      (modulePullback B S hS ψ).obj ((modulePullback B S hS φV).obj N))
    (w' : (modulePullback B S hS ψ').obj ((modulePullback B S hS φV).obj M) ⟶
      (modulePullback B S hS ψ').obj ((modulePullback B S hS φV).obj N))
    (hx : QuasiCoherentDescent.restrictForm B S hS p φ (p ≫ φ) rfl
        (QuasiCoherentDescent.factorForm B S hS ψ φV φ hφ w) =
      QuasiCoherentDescent.restrictForm B S hS q φ' (p ≫ φ) hsnd
        (QuasiCoherentDescent.factorForm B S hS ψ' φV φ' hφ' w')) :
    (modulePullback B S hS p).map w ≫
        (QuasiCoherentDescent.canonicalComparison p q ψ ψ' hpq
          ((modulePullback B S hS φV).obj N)).hom =
      (QuasiCoherentDescent.canonicalComparison p q ψ ψ' hpq
          ((modulePullback B S hS φV).obj M)).hom ≫
        (modulePullback B S hS q).map w' := by
  refine QuasiCoherentDescent.canonicalComparison_naturality_of_restrictForm_eq B S hS p q ψ ψ'
    (p ≫ ψ) rfl hpq.symm hpq w w' ?_
  refine QuasiCoherentDescent.factorForm_injective B S hS (p ≫ ψ) φV (p ≫ φ) hst ?_
  exact ((QuasiCoherentDescent.restrictForm_factorForm B S hS p ψ φV φ hφ (p ≫ ψ) rfl
      (p ≫ φ) rfl hst w).symm.trans hx).trans
    (QuasiCoherentDescent.restrictForm_factorForm B S hS q ψ' φV φ' hφ' (p ≫ ψ) hpq.symm
      (p ≫ φ) hsnd hst w')

/-- **A family whose readings through Stacks 03LU agree on the pairwise fibre products satisfies
the pairwise condition of Stacks 04W3.** -/
theorem isPairwiseCompatible_of_restrictForm_eq (φV : V ⟶ X) (Yi : I → AlgebraicSpaces B S hS)
    (ψ : ∀ i, Yi i ⟶ V) (φ : ∀ i, Yi i ⟶ X) (hφ : ∀ i, ψ i ≫ φV = φ i)
    (w : ∀ i, (modulePullback B S hS (ψ i)).obj ((modulePullback B S hS φV).obj M) ⟶
      (modulePullback B S hS (ψ i)).obj ((modulePullback B S hS φV).obj N))
    (hx : ∀ i j (h : QuasiCoherentDescent.pairSnd B S hS Yi ψ i j ≫ φ j =
        QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i),
      QuasiCoherentDescent.restrictForm B S hS (QuasiCoherentDescent.pairFst B S hS Yi ψ i j)
          (φ i) (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i) rfl
          (QuasiCoherentDescent.factorForm B S hS (ψ i) φV (φ i) (hφ i) (w i)) =
        QuasiCoherentDescent.restrictForm B S hS (QuasiCoherentDescent.pairSnd B S hS Yi ψ i j)
          (φ j) (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i) h
          (QuasiCoherentDescent.factorForm B S hS (ψ j) φV (φ j) (hφ j) (w j))) :
    QuasiCoherentDescent.IsPairwiseCompatible B S hS Yi ψ w := by
  intro i j
  have hc := QuasiCoherentDescent.pair_condition B S hS Yi ψ i j
  have hst : (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ ψ i) ≫ φV =
      QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i :=
    (Category.assoc _ _ _).trans
      (congrArg (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ ·) (hφ i))
  have hsnd : QuasiCoherentDescent.pairSnd B S hS Yi ψ i j ≫ φ j =
      QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i :=
    (congrArg (QuasiCoherentDescent.pairSnd B S hS Yi ψ i j ≫ ·) (hφ j)).symm.trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ φV) hc.symm).trans hst))
  exact canonicalComparison_naturality_of_restrictForm_factorForm_eq B S hS φV
    (QuasiCoherentDescent.pairFst B S hS Yi ψ i j) (QuasiCoherentDescent.pairSnd B S hS Yi ψ i j)
    (ψ i) (ψ j) hc (φ i) (φ j) (hφ i) (hφ j) hst hsnd (w i) (w j) (hx i j hsnd)

/-- **Gluing morphisms of restrictions along an étale covering.**  Let `(ψ i : Y i ⟶ V)` be an
étale covering of an algebraic space `φV : V ⟶ X` over `X`, with `φ i = ψ i ≫ φV`, and let
`x i : (φ i)^*M ⟶ (φ i)^*N` be morphisms whose restricted readings to every pairwise fibre product
`Y i ×_V Y j` agree.  Then there is exactly one `t : φV^*M ⟶ φV^*N` whose restricted reading
along each `ψ i` is `x i`. -/
theorem existsUnique_restrictForm_eq (φV : V ⟶ X) (Yi : I → AlgebraicSpaces B S hS)
    (ψ : ∀ i, Yi i ⟶ V) (hψ : ∀ i, IsEtale B S hS (ψ i).hom)
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (ψ i).hom))
    (φ : ∀ i, Yi i ⟶ X) (hφ : ∀ i, ψ i ≫ φV = φ i)
    (x : ∀ i, (modulePullback B S hS (φ i)).obj M ⟶ (modulePullback B S hS (φ i)).obj N)
    (hx : ∀ i j (h : QuasiCoherentDescent.pairSnd B S hS Yi ψ i j ≫ φ j =
        QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i),
      QuasiCoherentDescent.restrictForm B S hS (QuasiCoherentDescent.pairFst B S hS Yi ψ i j)
          (φ i) (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i) rfl (x i) =
        QuasiCoherentDescent.restrictForm B S hS (QuasiCoherentDescent.pairSnd B S hS Yi ψ i j)
          (φ j) (QuasiCoherentDescent.pairFst B S hS Yi ψ i j ≫ φ i) h (x j)) :
    ∃! t : (modulePullback B S hS φV).obj M ⟶ (modulePullback B S hS φV).obj N,
      ∀ i, QuasiCoherentDescent.restrictForm B S hS (ψ i) φV (φ i) (hφ i) t = x i := by
  have hfac : ∀ i, ∃ w, QuasiCoherentDescent.factorForm B S hS (ψ i) φV (φ i) (hφ i) w = x i :=
    fun i => QuasiCoherentDescent.exists_factorForm_eq B S hS _ _ _ _ (x i)
  choose w hw using hfac
  obtain ⟨t, ht⟩ := QuasiCoherentDescent.exists_modulePullback_map_eq B S hS Yi ψ hψ
    (QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction.toPair B S hS _ _ hψ
      (modulePullbackCompIsoEtaleRestriction B S hS))
    hcov w (isPairwiseCompatible_of_restrictForm_eq B S hS φV Yi ψ φ hφ w fun i j h =>
      (congrArg (QuasiCoherentDescent.restrictForm B S hS _ (φ i) _ rfl) (hw i)).trans
        ((hx i j h).trans (congrArg (QuasiCoherentDescent.restrictForm B S hS _ (φ j) _ h)
          (hw j)).symm))
  have hread : ∀ i, QuasiCoherentDescent.restrictForm B S hS (ψ i) φV (φ i) (hφ i) t = x i :=
    fun i => (congrArg (QuasiCoherentDescent.factorForm B S hS (ψ i) φV (φ i) (hφ i))
      (ht i)).trans (hw i)
  refine ⟨t, hread, fun t' ht' => ?_⟩
  refine QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS Yi ψ hcov
    t' t fun i => ?_
  exact QuasiCoherentDescent.factorForm_injective B S hS (ψ i) φV (φ i) (hφ i)
    ((ht' i).trans (hread i).symm)

end Glue

variable {X : AlgebraicSpaces B S hS}

/-- **The presheaf `SheafHom_{𝒪_X}(M, N)` on the spaces-étale site of `X`.**  Its sections over
`φ : V ⟶ X` étale are the `𝒪_V`-linear maps `φ^*M ⟶ φ^*N`, and its restriction along a
morphism `V₂ ⟶ V` over `X` is pullback of morphisms read through the comparison of
Stacks 03LU.  It is the relative Hom functor `AlgebraicGeometry.Space.moduleHomOver` restricted
to the spaces étale over `X`. -/
abbrev spacesEtaleModuleHom (M N : Modules.{u, u} B S hS X.1 X.2) :
    (SpacesEtale B S hS X)ᵒᵖ ⥤ Type (u + 1) :=
  (SpacesEtale.inclusion B S hS X).op ⋙ moduleHomOver (modulePushforwardCoherence B S hS) M N

/-- The restriction maps of `AlgebraicGeometry.Space.spacesEtaleModuleHom` are the restricted
readings of Stacks 03LU along the factorization of the structure morphisms. -/
theorem spacesEtaleModuleHom_map_eq (M N : Modules.{u, u} B S hS X.1 X.2)
    {A C : SpacesEtale B S hS X} (g : A ⟶ C)
    (θ : (modulePullback B S hS ((SpacesEtale.inclusion B S hS X).obj C).hom).obj M ⟶
      (modulePullback B S hS ((SpacesEtale.inclusion B S hS X).obj C).hom).obj N) :
    (spacesEtaleModuleHom B S hS M N).map g.op θ =
      QuasiCoherentDescent.restrictForm B S hS ((SpacesEtale.toSpaces B S hS X).map g)
        ((SpacesEtale.inclusion B S hS X).obj C).hom ((SpacesEtale.inclusion B S hS X).obj A).hom
        (SpacesEtale.toSpaces_map_comp_structure B S hS X g) θ :=
  conjHom_modulePullbackTriangle_eq_restrictForm B S hS _ θ

/-! ### The pairwise fibre product of a covering family, as an object of the site -/

/-- The pairwise fibre product `Y i ×_V Y j` of two members of a family of morphisms of the
spaces-étale site with common target `V`, as an object of the site, over `X` through the first
factor. -/
private noncomputable abbrev homSheafPb {V : SpacesEtale B S hS X} {I : Type*}
    (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V) (i j : I) : SpacesEtale B S hS X :=
  ⟨Over.mk (QuasiCoherentDescent.pairFst B S hS
      (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
      (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j ≫
        ((SpacesEtale.inclusion B S hS X).obj (Xi i)).hom),
    isEtale_comp B S hS
      (isEtale_of_isPullback B S hS _ _ _ _
        (AlgebraicSpaces.isPullback_fiberProduct B S hS
          ((SpacesEtale.toSpaces B S hS X).map (f i))
          ((SpacesEtale.toSpaces B S hS X).map (f j))).flip
        (SpacesEtale.isEtale_toSpaces_map B S hS X (f j)))
      (Xi i).property⟩

/-- The two projections of a pairwise fibre product have equal composites with the structure
morphisms. -/
private theorem homSheafPb_snd_comp {V : SpacesEtale B S hS X} {I : Type*}
    (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V) (i j : I) :
    QuasiCoherentDescent.pairSnd B S hS (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
        (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j ≫
        ((SpacesEtale.inclusion B S hS X).obj (Xi j)).hom =
      QuasiCoherentDescent.pairFst B S hS (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
        (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j ≫
        ((SpacesEtale.inclusion B S hS X).obj (Xi i)).hom := by
  rw [← SpacesEtale.toSpaces_map_comp_structure B S hS X (f i),
    ← SpacesEtale.toSpaces_map_comp_structure B S hS X (f j), ← Category.assoc, ← Category.assoc,
    QuasiCoherentDescent.pair_condition B S hS _ _ i j]

/-- The first projection of `homSheafPb`, as a morphism of the site. -/
private noncomputable def homSheafPbFst {V : SpacesEtale B S hS X} {I : Type*}
    (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V) (i j : I) :
    homSheafPb B S hS Xi f i j ⟶ Xi i :=
  ObjectProperty.homMk (Over.homMk (QuasiCoherentDescent.pairFst B S hS
    (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
    (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j) rfl)

/-- The second projection of `homSheafPb`, as a morphism of the site. -/
private noncomputable def homSheafPbSnd {V : SpacesEtale B S hS X} {I : Type*}
    (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V) (i j : I) :
    homSheafPb B S hS Xi f i j ⟶ Xi j :=
  ObjectProperty.homMk (Over.homMk (QuasiCoherentDescent.pairSnd B S hS
    (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
    (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j)
    (homSheafPb_snd_comp B S hS Xi f i j))

/-- The square of the two projections of `homSheafPb` commutes in the site. -/
private theorem homSheafPb_w {V : SpacesEtale B S hS X} {I : Type*}
    (Xi : I → SpacesEtale B S hS X) (f : ∀ i, Xi i ⟶ V) (i j : I) :
    homSheafPbFst B S hS Xi f i j ≫ f i = homSheafPbSnd B S hS Xi f i j ≫ f j :=
  (SpacesEtale.inclusion B S hS X).map_injective <| Over.OverMorphism.ext <|
    QuasiCoherentDescent.pair_condition B S hS
      (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
      (fun i => (SpacesEtale.toSpaces B S hS X).map (f i)) i j

/-! ### The sheaf property -/

/-- The sheaf condition of `AlgebraicGeometry.Space.spacesEtaleModuleHom` for a covering family
of the spaces-étale site: a compatible family of morphisms of the restrictions glues to a unique
morphism. -/
private theorem isSheafFor_spacesEtaleModuleHom (M N : Modules.{u, u} B S hS X.1 X.2)
    {V : SpacesEtale B S hS X} {I : Type (u + 1)} (Xi : I → SpacesEtale B S hS X)
    (f : ∀ i, Xi i ⟶ V)
    (hcov : IsEtaleCovering B S hS
      (fun i => ((SpacesEtale.toSpaces B S hS X).obj (Xi i)).obj)
      (fun i => ((SpacesEtale.toSpaces B S hS X).map (f i)).hom)) :
    Presieve.IsSheafFor (spacesEtaleModuleHom B S hS M N) (Presieve.ofArrows Xi f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  obtain ⟨t, ht, hu⟩ := existsUnique_restrictForm_eq B S hS (M := M) (N := N)
    ((SpacesEtale.inclusion B S hS X).obj V).hom
    (fun i => (SpacesEtale.toSpaces B S hS X).obj (Xi i))
    (fun i => (SpacesEtale.toSpaces B S hS X).map (f i))
    (fun i => SpacesEtale.isEtale_toSpaces_map B S hS X (f i)) hcov
    (fun i => ((SpacesEtale.inclusion B S hS X).obj (Xi i)).hom)
    (fun i => SpacesEtale.toSpaces_map_comp_structure B S hS X (f i)) x
    (fun i j _ =>
      (spacesEtaleModuleHom_map_eq B S hS M N (homSheafPbFst B S hS Xi f i j) (x i)).symm.trans
        ((hx i j (homSheafPb B S hS Xi f i j) (homSheafPbFst B S hS Xi f i j)
          (homSheafPbSnd B S hS Xi f i j) (homSheafPb_w B S hS Xi f i j)).trans
          (spacesEtaleModuleHom_map_eq B S hS M N (homSheafPbSnd B S hS Xi f i j) (x j))))
  exact ⟨t, fun i => (spacesEtaleModuleHom_map_eq B S hS M N (f i) t).trans (ht i),
    fun t' h => hu t' fun i => (spacesEtaleModuleHom_map_eq B S hS M N (f i) t').symm.trans (h i)⟩

/-- **`SheafHom_{𝒪_X}(M, N)` is a sheaf on the spaces-étale site of `X`.**  For two arbitrary
`𝒪_X`-modules `M` and `N`, the presheaf `V ↦ Hom_{𝒪_V}(M|_V, N|_V)` of
`AlgebraicGeometry.Space.spacesEtaleModuleHom` satisfies the sheaf condition for every covering
of the spaces-étale site. -/
theorem isSheaf_spacesEtaleModuleHom (M N : Modules.{u, u} B S hS X.1 X.2) :
    Presieve.IsSheaf (SpacesEtale.topology B S hS X) (spacesEtaleModuleHom B S hS M N) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro V _ ⟨E, rfl, hE⟩
  exact isSheafFor_spacesEtaleModuleHom B S hS M N E.X E.f
    (SpacesEtale.isEtaleCovering_of_isCovering B S hS X E.X E.f hE)

end AlgebraicGeometry.Space

end
