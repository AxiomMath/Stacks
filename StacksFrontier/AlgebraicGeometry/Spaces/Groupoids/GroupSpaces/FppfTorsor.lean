module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PseudoTorsors
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors

/-!
# Fppf torsors of algebraic spaces and torsors on the big fppf site

An action of a group algebraic space `G` on an algebraic space `X` over a scheme `S` is a
torsor in the fppf topology exactly when the sheaf of sections of `X` is a torsor, in the
sheaf-theoretic sense, under the sheaf of groups of sections of `G` on the big fppf site of
`S`.

The base of the action is the terminal presheaf on the big fppf site of `S`, so the sections
of an algebraic space over a test object `T` of the site are the morphisms into it from the
Yoneda presheaf of `T`, and the group action in the slice induces an action on sections.

## Main definitions

* `AlgebraicGeometry.Space.yonedaOverTerminal` presents a test object of the big fppf site of
  `S` as an object over the terminal presheaf, and
  `AlgebraicGeometry.Space.overTerminalSectionEquiv` identifies the sections of an object over
  the terminal presheaf with the morphisms into it from that presentation.
* `AlgebraicGeometry.Space.sectionAction` is the induced action of the sections of a group
  algebraic space on the sections of an algebraic space it acts on.
* `AlgebraicGeometry.Space.IsSiteTorsor` says that the sheaf of sections of the acted-on
  algebraic space is a torsor in the sense of Tag 03AH for the sheaf of groups of sections of
  the group algebraic space, with both underlying sheaves and both actions identified.

## Main results

* `AlgebraicGeometry.Space.isFppfTorsor_iff_siteTorsor` is **Stacks 04TZ**: an fppf torsor of
  algebraic spaces is exactly a torsor on the big fppf site.

## Implementation notes

The site-side condition records the identifications of the underlying sheaves as natural
isomorphisms and requires the two actions to agree over every test object; without that last
requirement a torsor structure unrelated to the given action of algebraic spaces could serve
as a witness.

Both directions of the comparison pass through the object `Over.mk (𝟙 (B.obj hS))` of the
site, which is terminal there and whose Yoneda presheaf is therefore a second terminal
presheaf. The every-étale-chart conditions of Tag 03MJ for a morphism into a terminal
presheaf do not depend on which terminal presheaf is chosen
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isTerminal`), and neither does joint
surjectivity on points, so an fppf covering of one terminal presheaf is an fppf covering of
the other. That reduction lets the geometric side be read off the site's chosen covering
families through `AlgebraicGeometry.Space.yoneda_fppfCovering_mem_fppfPrecoverage` and
`AlgebraicGeometry.BigFppfSite.generate_mem_topology_of_isFppfCovering`.

## References

* [Stacks Project, Tag 04TZ](https://stacks.math.columbia.edu/tag/04TZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sections of an algebraic space over the terminal presheaf -/

/-- A test object of the big fppf site of `S`, presented as an object over the terminal
presheaf through its Yoneda presheaf. -/
noncomputable abbrev yonedaOverTerminal (T : BigFppfOver B S hS) :
    Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  Over.mk (terminal.from (yoneda.obj T))

/-- The sections over a test object `T` of an object of the slice over the terminal presheaf
are the morphisms into it from `T`, presented over the terminal presheaf: the structure
morphisms are forced, so this is the Yoneda identification. -/
noncomputable def overTerminalSectionEquiv
    (F : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) (T : BigFppfOver B S hS) :
    (yonedaOverTerminal B S hS T ⟶ F) ≃ F.left.obj (op T) where
  toFun f := yonedaEquiv (Over.Hom.left f)
  invFun g := Over.homMk (yonedaEquiv.symm g) (Subsingleton.elim _ _)
  left_inv f := Over.OverMorphism.ext <|
    (yonedaEquiv (X := T) (F := F.left)).symm_apply_apply f.left
  right_inv g := (yonedaEquiv (X := T) (F := F.left)).apply_symm_apply g

/-- Restricting a section along a morphism of the site corresponds, under
`AlgebraicGeometry.Space.overTerminalSectionEquiv`, to precomposing the morphism it
represents. -/
theorem overTerminalSectionEquiv_map
    (F : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) {U V : (BigFppfOver B S hS)ᵒᵖ}
    (f : U ⟶ V) (φ : yonedaOverTerminal B S hS (unop U) ⟶ F) :
    F.left.map f (overTerminalSectionEquiv B S hS F (unop U) φ) =
      overTerminalSectionEquiv B S hS F (unop V)
        ((Over.homMk (yoneda.map f.unop) (Subsingleton.elim _ _) :
          yonedaOverTerminal B S hS (unop V) ⟶ yonedaOverTerminal B S hS (unop U)) ≫ φ) :=
  yonedaEquiv_naturality' _ _

/-- The action of the sections of a group algebraic space over the terminal presheaf on the
sections of an algebraic space it acts on, over a test object of the big fppf site of `S`. -/
noncomputable def sectionAction
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (T : BigFppfOver B S hS) (g : G.left.obj (op T)) (x : X.left.obj (op T)) :
    X.left.obj (op T) :=
  overTerminalSectionEquiv B S hS X T
    ((overTerminalSectionEquiv B S hS G T).symm g •
      (overTerminalSectionEquiv B S hS X T).symm x)

/-- `AlgebraicGeometry.Space.sectionAction` unfolded: it is the action in the slice, read
through the identification of sections with morphisms. -/
theorem sectionAction_eq
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (T : BigFppfOver B S hS) (g : G.left.obj (op T)) (x : X.left.obj (op T)) :
    sectionAction B S hS G X T g x =
      overTerminalSectionEquiv B S hS X T
        ((overTerminalSectionEquiv B S hS G T).symm g •
          (overTerminalSectionEquiv B S hS X T).symm x) :=
  rfl

/-- The action on sections is the action in the slice: it carries the morphisms representing
two sections to the morphism representing the section they act to. -/
@[simp]
theorem sectionAction_apply
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (T : BigFppfOver B S hS) (g : yonedaOverTerminal B S hS T ⟶ G)
    (x : yonedaOverTerminal B S hS T ⟶ X) :
    sectionAction B S hS G X T (overTerminalSectionEquiv B S hS G T g)
        (overTerminalSectionEquiv B S hS X T x) =
      overTerminalSectionEquiv B S hS X T (g • x) := by
  rw [sectionAction_eq, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-! ### The sheaves of sections -/

/-- A group object in the slice over the terminal presheaf whose underlying presheaf is a
sheaf, viewed as a sheaf of groups on the big fppf site of `S`: its sections over a test
object form a group because they are the morphisms into a group object. -/
private noncomputable def sectionSheafOfGroups
    (G : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.left) :
    SheafOfGroups (BigFppfOver.topology B S hS) where
  presheaf := G.left
  isSheaf := hG
  group T := Equiv.group (overTerminalSectionEquiv B S hS G (unop T)).symm
  map_mul := by
    intro U V f g₁ g₂
    rw [Equiv.mul_def (overTerminalSectionEquiv B S hS G (unop U)).symm g₁ g₂]
    simp only [Equiv.symm_symm]
    rw [overTerminalSectionEquiv_map]
    have hres : ∀ a : G.left.obj U,
        G.left.map f a = overTerminalSectionEquiv B S hS G (unop V)
          ((Over.homMk (yoneda.map f.unop) (Subsingleton.elim _ _) :
            yonedaOverTerminal B S hS (unop V) ⟶
              yonedaOverTerminal B S hS (unop U)) ≫
            (overTerminalSectionEquiv B S hS G (unop U)).symm a) := by
      intro a
      have h := overTerminalSectionEquiv_map B S hS G f
        ((overTerminalSectionEquiv B S hS G (unop U)).symm a)
      rwa [Equiv.apply_symm_apply] at h
    rw [hres g₁, hres g₂, Equiv.mul_def (overTerminalSectionEquiv B S hS G (unop V)).symm]
    simp only [Equiv.symm_symm, Equiv.symm_apply_apply]
    exact congrArg _ (MonObj.comp_mul _ _ _)

/-- The group structure on the sections of a group object over the terminal presheaf has the
identity morphism as its unit. -/
private theorem sectionSheafOfGroups_one
    (G : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.left)
    (T : (BigFppfOver B S hS)ᵒᵖ) :
    (1 : (sectionSheafOfGroups B S hS G hG).presheaf.obj T) =
      overTerminalSectionEquiv B S hS G (unop T) 1 :=
  rfl

/-- The group structure on the sections of a group object over the terminal presheaf is the
one transported from the morphisms into it. -/
private theorem sectionSheafOfGroups_mul
    (G : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G]
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G.left)
    (T : (BigFppfOver B S hS)ᵒᵖ)
    (g h : (sectionSheafOfGroups B S hS G hG).presheaf.obj T) :
    g * h = overTerminalSectionEquiv B S hS G (unop T)
      ((overTerminalSectionEquiv B S hS G (unop T)).symm g *
        (overTerminalSectionEquiv B S hS G (unop T)).symm h) :=
  rfl

/-- A pseudo-torsor action of algebraic spaces over the terminal presheaf, viewed as a
pseudo-torsor of sheaves on the big fppf site of `S` under the sheaf of groups of sections. -/
private noncomputable def sectionPseudoTorsor
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left)
    (hp : IsPseudoTorsor G X) :
    PseudoTorsor (sectionSheafOfGroups B S hS G hG.isSheaf) where
  presheaf := X.left
  isSheaf := hX.isSheaf
  act U g x := sectionAction B S hS G X (unop U) g x
  one_act := by
    intro T s
    obtain ⟨b, rfl⟩ := (overTerminalSectionEquiv B S hS X (unop T)).surjective s
    rw [sectionSheafOfGroups_one, sectionAction_apply, one_smul]
  mul_act := by
    intro T g h s
    rw [sectionSheafOfGroups_mul]
    obtain ⟨a, rfl⟩ := (overTerminalSectionEquiv B S hS G (unop T)).surjective g
    obtain ⟨c, rfl⟩ := (overTerminalSectionEquiv B S hS G (unop T)).surjective h
    obtain ⟨b, rfl⟩ := (overTerminalSectionEquiv B S hS X (unop T)).surjective s
    simp only [Equiv.symm_apply_apply, sectionAction_apply]
    rw [mul_smul]
  naturality := by
    intro U V f g x
    obtain ⟨a, rfl⟩ := (overTerminalSectionEquiv B S hS G (unop U)).surjective g
    obtain ⟨b, rfl⟩ := (overTerminalSectionEquiv B S hS X (unop U)).surjective x
    change X.left.map f (sectionAction B S hS G X (unop U)
        (overTerminalSectionEquiv B S hS G (unop U) a)
        (overTerminalSectionEquiv B S hS X (unop U) b)) =
      sectionAction B S hS G X (unop V)
        (G.left.map f (overTerminalSectionEquiv B S hS G (unop U) a))
        (X.left.map f (overTerminalSectionEquiv B S hS X (unop U) b))
    simp only [sectionAction_apply, overTerminalSectionEquiv_map,
      CategoryTheory.ModObj.comp_smul]
  simplyTransitive := by
    intro T _ s t
    obtain ⟨x, rfl⟩ := (overTerminalSectionEquiv B S hS X (unop T)).surjective s
    obtain ⟨y, rfl⟩ := (overTerminalSectionEquiv B S hS X (unop T)).surjective t
    obtain ⟨g, hg, huniq⟩ := (isPseudoTorsor_iff_points B S hS
      (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) G X).mp hp (unop T)
      (terminal.from (yoneda.obj (unop T))) x y
    refine ⟨overTerminalSectionEquiv B S hS G (unop T) g, ?_, ?_⟩
    · change sectionAction B S hS G X (unop T)
          (overTerminalSectionEquiv B S hS G (unop T) g)
          (overTerminalSectionEquiv B S hS X (unop T) x) =
        overTerminalSectionEquiv B S hS X (unop T) y
      rw [sectionAction_apply, hg]
    · intro g' hg'
      obtain ⟨a, rfl⟩ := (overTerminalSectionEquiv B S hS G (unop T)).surjective g'
      replace hg' : sectionAction B S hS G X (unop T)
          (overTerminalSectionEquiv B S hS G (unop T) a)
          (overTerminalSectionEquiv B S hS X (unop T) x) =
        overTerminalSectionEquiv B S hS X (unop T) y := hg'
      rw [sectionAction_apply] at hg'
      exact congrArg _
        (huniq a ((overTerminalSectionEquiv B S hS X (unop T)).injective hg'))

/-! ### Changing the terminal presheaf -/

/-- An fppf covering of a terminal presheaf is an fppf covering of any other terminal
presheaf: the flatness and finite-presentation conditions of Tag 03MJ see only the charts of
the sources, and the two terminal presheaves have the same points. -/
private theorem isFppfCovering_of_isTerminal
    {I : Type v} {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsTerminal F) (hF' : IsTerminal F') (hF'alg : IsAlgebraicSpace B S hS F')
    {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : ∀ i, X i ⟶ F) (f' : ∀ i, X i ⟶ F')
    (h : IsFppfCovering B S hS X f) :
    IsFppfCovering B S hS X f' where
  target_isAlgebraicSpace := hF'alg
  source_isAlgebraicSpace := h.source_isAlgebraicSpace
  flat i := holdsOnEveryEtaleChart_of_isTerminal B S hS hF hF' (f i) (f' i) (h.flat i)
  locallyOfFinitePresentation i :=
    holdsOnEveryEtaleChart_of_isTerminal B S hS hF hF' (f i) (f' i)
      (h.locallyOfFinitePresentation i)
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun w => ?_
    have hw : pointsMap B S hS F' (hF.uniqueUpToIso hF').inv w ∈
        ⋃ i, Set.range (pointsMap B S hS (X i) (f i)) := by
      rw [h.jointly_surjective]
      exact Set.mem_univ _
    obtain ⟨i, p, hp⟩ := Set.mem_iUnion.mp hw
    refine Set.mem_iUnion.mpr ⟨i, p, ?_⟩
    have hfe : f' i = f i ≫ (hF.uniqueUpToIso hF').hom := hF'.hom_ext _ _
    have hcancel : pointsMap B S hS F (hF.uniqueUpToIso hF').hom
        (pointsMap B S hS F' (hF.uniqueUpToIso hF').inv w) = w := by
      rw [← Function.comp_apply (f := pointsMap B S hS F (hF.uniqueUpToIso hF').hom),
        ← pointsMap_comp, Iso.inv_hom_id, pointsMap_id, id_eq]
    rw [hfe, pointsMap_comp, Function.comp_apply, hp, hcancel]

/-! ### The comparison -/

/-- A chosen covering family of the big fppf site, read in the big fppf site of `S` through
the terminal object `Over.mk (𝟙 (B.obj hS))`, is an fppf covering of algebraic spaces. -/
private theorem isFppfCovering_yoneda_map_of_isCovering
    {E : PreZeroHypercover.{u + 1} (B.obj hS)} (hE : B.IsCovering ⟨B.obj hS, E⟩) :
    IsFppfCovering B S hS (fun i => yoneda.obj (Over.mk (E.f i) : BigFppfOver B S hS))
      (fun i => yoneda.map (Over.homMk (E.f i) (Category.comp_id _) :
        (Over.mk (E.f i) : BigFppfOver B S hS) ⟶ Over.mk (𝟙 (B.obj hS)))) where
  target_isAlgebraicSpace := isAlgebraicSpace_yoneda B S hS _
  source_isAlgebraicSpace i := isAlgebraicSpace_yoneda B S hS _
  flat i := isFlat_yoneda_map B S hS _
    ((BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering B hE).2 i).1
  locallyOfFinitePresentation i := isLocallyOfFinitePresentation_yoneda_map B S hS _
    ((BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering B hE).2 i).2
  jointly_surjective := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨i, y, hy⟩ :=
      (BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering B hE).1
        (pointsToScheme B S hS (Over.mk (𝟙 (B.obj hS))) w)
    obtain ⟨p, hp⟩ := surjective_pointsToScheme B S hS (Over.mk (E.f i)) y
    refine Set.mem_iUnion.mpr ⟨i, p, ?_⟩
    apply injective_pointsToScheme B S hS (Over.mk (𝟙 (B.obj hS)))
    rwa [pointsToScheme_pointsMap_yoneda, hp]

/-- A pseudo-torsor whose structure morphism has sections after an fppf covering of the
terminal presheaf has sections after a covering sieve of every object of the big fppf site of
`S`. -/
private theorem exists_sieve_nonempty_sections_of_isFppfCovering
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Bᵢ i ⟶ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (hcover : IsFppfCovering B S hS Bᵢ f)
    (hsections : ∀ i, Nonempty (𝟙_ (Over (Bᵢ i)) ⟶ (Over.pullback (f i)).obj X)) :
    ∀ U : BigFppfOver B S hS, ∃ R ∈ BigFppfOver.topology B S hS U,
      ∀ ⦃V : BigFppfOver B S hS⦄ ⦃g : V ⟶ U⦄, R g → Nonempty (X.left.obj (op V)) := by
  classical
  obtain ⟨T, a, hT⟩ := exists_fppfCovering_scheme_refinement B S hS Bᵢ f hcover
  let U₀ : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let q (i : I) : T i ⟶ U₀ := Over.homMk (T i).hom (Category.comp_id _)
  have hcov : IsFppfCovering B S hS (fun i => yoneda.obj (T i)) (fun i => yoneda.map (q i)) :=
    isFppfCovering_of_isTerminal B S hS terminalIsTerminal
      ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _)
      (isAlgebraicSpace_yoneda B S hS U₀) _ _ hT
  let E : PreZeroHypercover.{u + 1} U₀.left :=
    ⟨I, fun i => (T i).left, fun i => (q i).left⟩
  have hE : AlgebraicGeometry.IsFppfCovering (⟨U₀.left, E⟩ : Covering B.Schemes) := by
    rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    exact yoneda_fppfCovering_mem_fppfPrecoverage B S hS T U₀ q hcov
  let R₀ : Sieve U₀ := Sieve.ofArrows T q
  have hR₀ : R₀ ∈ BigFppfOver.topology B S hS U₀ := by
    rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    simpa [R₀, E, PreZeroHypercover.presieve₀] using
      B.generate_mem_topology_of_isFppfCovering E hE
  intro U
  refine ⟨R₀.pullback (Over.homMk U.hom (Category.comp_id _)),
    (BigFppfOver.topology B S hS).pullback_stable _ hR₀, ?_⟩
  intro V g hg
  have hg₀ : R₀ (g ≫ Over.homMk U.hom (Category.comp_id _)) := by simpa using hg
  obtain ⟨i, e, -⟩ := Sieve.ofArrows.exists hg₀
  obtain ⟨s⟩ := hsections i
  exact ⟨X.left.map e.op (yonedaEquiv (a i ≫ s.left ≫ pullback.fst X.hom (f i)))⟩

/-- A torsor of sheaves whose sheaf of groups and whose underlying sheaf are the sheaves of
sections of a group algebraic space and of an algebraic space it acts on, compatibly with the
actions, arises from a pseudo-torsor action. -/
private theorem isPseudoTorsor_of_siteTorsorData
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (H : SheafOfGroups (BigFppfOver.topology B S hS)) (F : PseudoTorsor H)
    (eG : H.presheaf ≅ G.left) (eX : F.presheaf ≅ X.left)
    (hact : ∀ (T : BigFppfOver B S hS) (g : H.presheaf.obj (op T))
      (x : F.presheaf.obj (op T)),
      eX.hom.app (op T) (F.act (op T) g x) =
        sectionAction B S hS G X T (eG.hom.app (op T) g) (eX.hom.app (op T) x)) :
    IsPseudoTorsor G X := by
  refine (isPseudoTorsor_iff_points B S hS
    (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) G X).2 fun T b x y => ?_
  obtain rfl : b = terminal.from (yoneda.obj T) := Subsingleton.elim _ _
  have hX : ∀ z, eX.hom.app (op T) (eX.inv.app (op T) z) = z := by simp
  have hG : ∀ z, eG.hom.app (op T) (eG.inv.app (op T) z) = z := by simp
  obtain ⟨gF, hgy, huniq⟩ := F.simplyTransitive (op T)
    ⟨eX.inv.app (op T) (overTerminalSectionEquiv B S hS X T x)⟩
    (eX.inv.app (op T) (overTerminalSectionEquiv B S hS X T x))
    (eX.inv.app (op T) (overTerminalSectionEquiv B S hS X T y))
  refine ⟨(overTerminalSectionEquiv B S hS G T).symm (eG.hom.app (op T) gF), ?_, ?_⟩
  · apply (overTerminalSectionEquiv B S hS X T).injective
    have h := hact T gF (eX.inv.app (op T) (overTerminalSectionEquiv B S hS X T x))
    rw [hgy, hX, hX] at h
    rw [h, sectionAction_eq, Equiv.symm_apply_apply]
  · intro g' hg'
    have h := hact T (eG.inv.app (op T) (overTerminalSectionEquiv B S hS G T g'))
      (eX.inv.app (op T) (overTerminalSectionEquiv B S hS X T x))
    rw [hX, hG, sectionAction_apply, hg'] at h
    have := huniq (eG.inv.app (op T) (overTerminalSectionEquiv B S hS G T g'))
      ((eX.app (op T)).toEquiv.injective (h.trans (hX _).symm))
    rw [Equiv.eq_symm_apply, ← hG (overTerminalSectionEquiv B S hS G T g'), this]

/-- An action of a group algebraic space over the terminal presheaf of the big fppf site of
`S` is a *torsor on the site* when the sheaf of sections of the acted-on algebraic space is a
torsor in the sense of Tag 03AH under the sheaf of groups of sections of the group algebraic
space, the two sheaves being identified with the given presheaves and the two actions
agreeing over every test object. -/
def IsSiteTorsor (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    [GrpObj G] [ModObj G X] : Prop :=
  ∃ (H : SheafOfGroups (BigFppfOver.topology B S hS)) (F : PseudoTorsor H)
    (eG : H.presheaf ≅ G.left) (eX : F.presheaf ≅ X.left),
      F.IsTorsor ∧
        ∀ (T : BigFppfOver B S hS) (g : H.presheaf.obj (op T))
          (x : F.presheaf.obj (op T)),
          eX.hom.app (op T) (F.act (op T) g x) =
            sectionAction B S hS G X T (eG.hom.app (op T) g) (eX.hom.app (op T) x)

/-- **Stacks 04TZ.** An action of a group algebraic space over `S` on an algebraic space over
`S` is an fppf torsor exactly when it is a torsor on the big fppf site of `S`. -/
@[stacks 04TZ "the whole statement: the biconditional over the base `S` itself, with the \
site-side condition read in the sense of Tag 03AH"]
theorem isFppfTorsor_iff_siteTorsor
    (hB : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)))
    (G X : Over (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) [GrpObj G] [ModObj G X]
    (hG : IsAlgebraicSpace B S hS G.left) (hX : IsAlgebraicSpace B S hS X.left) :
    IsFppfTorsor B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) hB G X hG hX ↔
      IsSiteTorsor B S hS G X := by
  constructor
  · rintro ⟨hp, I, Bᵢ, f, hBi, hcover, hsections⟩
    exact ⟨sectionSheafOfGroups B S hS G hG.isSheaf, sectionPseudoTorsor B S hS G X hG hX hp,
      Iso.refl _, Iso.refl _,
      exists_sieve_nonempty_sections_of_isFppfCovering B S hS Bᵢ f X hcover hsections,
      fun _ _ _ => rfl⟩
  · rintro ⟨H, F, eG, eX, hFT, hact⟩
    refine ⟨isPseudoTorsor_of_siteTorsorData B S hS G X H F eG eX hact, ?_⟩
    obtain ⟨R, hR, hRloc⟩ := hFT (Over.mk (𝟙 (B.obj hS)))
    obtain ⟨E, hE, hle⟩ := exists_covering_refining_sieve B
      ((B.topology.mem_over_iff R).1 hR)
    refine ⟨E.I₀, fun i => yoneda.obj (Over.mk (E.f i) : BigFppfOver B S hS),
      fun _ => terminal.from _, fun i => isAlgebraicSpace_yoneda B S hS _, ?_, ?_⟩
    · exact isFppfCovering_of_isTerminal B S hS
        ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _) terminalIsTerminal hB
        _ _ (isFppfCovering_yoneda_map_of_isCovering B S hS hE)
    · intro i
      have hqi : R (Over.homMk (E.f i) (Category.comp_id _) :
          (Over.mk (E.f i) : BigFppfOver B S hS) ⟶ Over.mk (𝟙 (B.obj hS))) :=
        (Sieve.overEquiv_iff R (E.f i)).1 (hle _ _ ⟨i⟩)
      obtain ⟨s⟩ := hRloc hqi
      refine ⟨Over.homMk (pullback.lift
        ((yonedaEquiv (X := (Over.mk (E.f i) : BigFppfOver B S hS)) (F := X.left)).symm
          (eX.hom.app (op (Over.mk (E.f i) : BigFppfOver B S hS)) s))
        (𝟙 (yoneda.obj (Over.mk (E.f i) : BigFppfOver B S hS))) (by subsingleton)) ?_⟩
      simp [pullback.lift_snd]

end AlgebraicGeometry.Space

end
