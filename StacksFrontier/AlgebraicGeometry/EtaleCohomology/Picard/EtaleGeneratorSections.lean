module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.PullbackGenerator
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcOverSiteDichotomy
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleOnSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnTheSmallEtaleSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.UnitTorsorsOfInvertibleModules

/-!
# Local generators of an invertible module on the étale site

Let `L` be an invertible module on a scheme `S`. For a scheme `T` over `S`, a *generator* of the
pullback `T^*L` is a global section `s` such that multiplication by `s` is a bijection
`𝒪_T(V) → (T^*L)(V)` on every open `V` of `T` (`Stacks.SheafOfModules.GeneratorSections`). This
file shows that the pullback map of sections of [Stacks, Tag 03DS] carries generators to
generators, which makes the generators of `L` a subpresheaf of the presheaf of sections of `L`
on the schemes over `S`.

## Main definitions

* `Stacks.EtaleGenerators.pullbackSectionsGenerator`: the pullback of a generator along a
  morphism of schemes over `S`, which is a generator.
* `Stacks.EtaleGenerators.IsUniversalGenerator`: a global section of `T^*L` whose pullback to
  every scheme `V` over `T` is a global generator of `V^*L`.
* `Stacks.EtaleGenerators.generatorPresheaf`: the presheaf of universal generators of `L` on the
  small étale site of `S`.

## Main results

* `Stacks.EtaleGenerators.bijective_smul_of_covering`: generation of global sections is fpqc
  local.
* `Stacks.EtaleGenerators.isSheaf_generatorPresheaf`: the universal generators form a sheaf on
  the small étale site.
* `Stacks.EtaleGenerators.exists_covering_nonempty_generatorPresheaf`: universal generators exist
  étale locally.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules (GeneratorSections generatorMapIso pullbackGenerator)

universe u v

namespace Stacks.EtaleGenerators

variable {S : Scheme.{u}} (L : S.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible S.presheaf
    (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).property L)

include hL in
/-- The pullback of an invertible module is invertible. -/
theorem isInvertible_pullback {T : Scheme.{u}} (f : T ⟶ S) :
    Stacks.SheafOfModules.IsInvertible T.presheaf
      (Stacks.RingedSpace.structureRingSheaf T.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj L) :=
  @Stacks.RingedSpace.isInvertible_modulePullback T.toRingedSpace S.toRingedSpace
    f.toLRSHom.toShHom L hL

/-- **The pullback of a global generator along a morphism of schemes over `S`, read through the
pullback map of sections of Tag 03DS, is a global generator.** -/
def pullbackSectionsGenerator {X Y : Over S} (g : X ⟶ Y)
    (s : GeneratorSections Y.left.toRingedSpace ((Scheme.Modules.pullback Y.hom).obj L) ⊤) :
    GeneratorSections X.left.toRingedSpace ((Scheme.Modules.pullback X.hom).obj L) ⊤ := by
  let e := (Scheme.Modules.pullbackComp g.left Y.hom).app L ≪≫
    (Scheme.Modules.pullbackCongr (Over.w g)).app L
  exact generatorMapIso e _ (pullbackGenerator g.left _ (isInvertible_pullback L hL Y.hom) ⊤ s)

/-- The section underlying the pullback of a generator is the pullback of its section along the
pullback map of sections of Tag 03DS. -/
theorem pullbackSectionsGenerator_val {X Y : Over S} (g : X ⟶ Y)
    (s : GeneratorSections Y.left.toRingedSpace ((Scheme.Modules.pullback Y.hom).obj L) ⊤) :
    (pullbackSectionsGenerator L hL g s).val = pullbackSectionsMap L g s.val := by
  rw [Stacks.Sites.pullbackSectionsMap_eq_topUnitMap]
  rfl

/-- The pullback map of sections of Tag 03DS along an identity is the identity. -/
theorem pullbackSectionsMap_id_apply (T : Over S)
    (m : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)) :
    pullbackSectionsMap L (𝟙 T) m = m :=
  congrArg (fun φ => φ m) ((quasiCoherentPresheafConstruction S L).functor.map_id (op T))

/-- The pullback maps of sections of Tag 03DS compose. -/
theorem pullbackSectionsMap_comp_apply {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : Γ((Scheme.Modules.pullback Z.hom).obj L, ⊤)) :
    pullbackSectionsMap L (f ≫ g) m = pullbackSectionsMap L f (pullbackSectionsMap L g m) :=
  congrArg (fun φ => φ m) ((quasiCoherentPresheafConstruction S L).functor.map_comp g.op f.op)

/-- **A universal generator** of the pullback of `L` to a scheme `T` over `S`: a global section
of `T^*L` whose pullback to every scheme `V` over `T` is a global generator of `V^*L`, in the
sense that multiplication by it is a bijection `Γ(V, 𝒪_V) → Γ(V, V^*L)`. -/
def IsUniversalGenerator {T : Over S} (s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)) : Prop :=
  ∀ ⦃V : Over S⦄ (g : V ⟶ T),
    Function.Bijective (fun r : Γ(V.left, ⊤) => r • pullbackSectionsMap L g s)

/-- A universal generator pulls back to a universal generator. -/
theorem IsUniversalGenerator.pullbackSectionsMap {T T' : Over S} (f : T ⟶ T')
    {s : Γ((Scheme.Modules.pullback T'.hom).obj L, ⊤)} (hs : IsUniversalGenerator L s) :
    IsUniversalGenerator L (pullbackSectionsMap L f s) := fun V g => by
  simpa only [pullbackSectionsMap_comp_apply] using hs (g ≫ f)

/-- A universal generator generates the global sections. -/
theorem IsUniversalGenerator.bijective {T : Over S}
    {s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)} (hs : IsUniversalGenerator L s) :
    Function.Bijective (fun r : Γ(T.left, ⊤) => r • s) := by
  simpa only [pullbackSectionsMap_id_apply] using hs (𝟙 T)

/-- A universal generator times a unit is a universal generator. -/
theorem IsUniversalGenerator.unit_smul {T : Over S}
    {s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)} (hs : IsUniversalGenerator L s)
    (a : (Γ(T.left, ⊤))ˣ) : IsUniversalGenerator L ((a : Γ(T.left, ⊤)) • s) := fun V g => by
  rw [pullbackSectionsMap_smul]
  exact Stacks.Cohomology.Generators.generator_smul_unit _ (hs g)
    (Units.map g.left.appTop.hom.toMonoidHom a)

include hL in
/-- **A global generator is a universal generator**: its pullback along any morphism of schemes
over `S` is again a global generator. -/
theorem isUniversalGenerator_of_generatorSections {T : Over S}
    (s : GeneratorSections T.left.toRingedSpace ((Scheme.Modules.pullback T.hom).obj L) ⊤) :
    IsUniversalGenerator L s.val := fun V g => by
  have h := (pullbackSectionsGenerator L hL g s).property ⊤ le_rfl
  have e := (Stacks.SheafOfModules.generator_restrict_self _ ⊤
    (pullbackSectionsGenerator L hL g s)).trans (pullbackSectionsGenerator_val L hL g s)
  exact (congrArg (fun m : Γ((Scheme.Modules.pullback V.hom).obj L, ⊤) =>
    Function.Bijective (fun r : Γ(V.left, ⊤) => r • m)) e).mp h

/-- The underlying type-valued presheaf of sections of `L` is an fpqc sheaf (Tag 03DT). -/
private theorem isSheaf_fpqc_quasiCoherentPresheafFunctor_forget
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf
      (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).property L) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S L ⋙ CategoryTheory.forget AddCommGrpCat.{u}) :=
  have : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (quasiCoherentPresheaf_isSheaf_fpqc' S L)

include hL in
/-- **Generation of global sections is fpqc local.** If `t` is a global section of `V^*L` whose
pullback to the members of an fpqc covering sieve of `V` are global generators, then `t` is a
global generator.  Both global functions and global sections of pullbacks of `L` are fpqc sheaves
on the schemes over `S` (Tag 03DT), so this is the sheaf condition for multiplication by `t`. -/
theorem bijective_smul_of_covering {V : Over S} (t : Γ((Scheme.Modules.pullback V.hom).obj L, ⊤))
    (R : Sieve V) (hR : R ∈ (Scheme.fpqcTopology.{u}.over S) V)
    (h : ∀ ⦃W : Over S⦄ (k : W ⟶ V), R k →
      Function.Bijective (fun r : Γ(W.left, ⊤) => r • pullbackSectionsMap L k t)) :
    Function.Bijective (fun r : Γ(V.left, ⊤) => r • t) := by
  let J := Scheme.fpqcTopology.{u}.over S
  let F : (Over V)ᵒᵖ ⥤ Type u := (Over.forget V).op ⋙ Stacks.Sites.globalSectionsOver S
  let G : (Over V)ᵒᵖ ⥤ Type u := (Over.forget V).op ⋙ (quasiCoherentPresheafFunctor S L ⋙
    CategoryTheory.forget AddCommGrpCat)
  have hF : Presheaf.IsSheaf (J.over V) F :=
    ((J.overPullback (Type u) V).obj ⟨_, Stacks.Sites.isSheaf_fpqcOver_globalSections S⟩).property
  have hG : Presheaf.IsSheaf (J.over V) G :=
    ((J.overPullback (Type u) V).obj
      ⟨_, isSheaf_fpqc_quasiCoherentPresheafFunctor_forget L hL⟩).property
  let φ : F ⟶ G :=
    { app W := ↾(fun r : F.obj W => (show Γ(W.unop.left.left, ⊤) from r) •
        pullbackSectionsMap L W.unop.hom t)
      naturality {W W'} f := by
        ext r
        show f.unop.left.left.appTop r • pullbackSectionsMap L W'.unop.hom t =
          pullbackSectionsMap L f.unop.left ((show Γ(W.unop.left.left, ⊤) from r) •
            pullbackSectionsMap L W.unop.hom t)
        rw [pullbackSectionsMap_smul, ← pullbackSectionsMap_comp_apply, Over.w f.unop] }
  have key := Stacks.Cohomology.Torsors.Generators.bijective_of_bijective_on_cover (J.over V)
    hF hG (U := Over.mk (𝟙 V)) ((Sieve.overEquiv _).symm R)
    (GrothendieckTopology.overEquiv_symm_mem_over _ _ _ hR) φ (fun W k hk => by
      have hk' : R k.left := (Sieve.overEquiv_symm_iff R k).1 hk
      have hW : W.hom = k.left := by simpa using (Over.w k).symm
      show Function.Bijective (fun r : Γ(W.left.left, ⊤) => r • pullbackSectionsMap L W.hom t)
      rw [hW]
      exact h k.left hk')
  change Function.Bijective (fun r : Γ(V.left, ⊤) => r • pullbackSectionsMap L (𝟙 V) t) at key
  simpa only [pullbackSectionsMap_id_apply] using key

/-! ### The presheaf of generators on the small étale site -/

/-- The presheaf `U ↦ Γ(U, U^*L)` of Tag 03DS on the small étale site of `S`, as a presheaf of
sets. -/
abbrev sectionsPresheaf : S.Etaleᵒᵖ ⥤ Type u :=
  (Scheme.Etale.forget S).op ⋙ (quasiCoherentPresheafConstruction S L).functor ⋙
    CategoryTheory.forget AddCommGrpCat

/-- The universal generators of `U^*L` over the étale `S`-schemes `U`. -/
def generatorSubfunctor : Subfunctor (sectionsPresheaf L) where
  obj U := {s | IsUniversalGenerator L (T := (Scheme.Etale.forget S).obj U.unop) s}
  map f _ hs := IsUniversalGenerator.pullbackSectionsMap L ((Scheme.Etale.forget S).map f.unop) hs

/-- **The presheaf of local generators of `L` on the small étale site of `S`**: its sections over
an étale `S`-scheme `U` are the universal generators of `U^*L`. -/
abbrev generatorPresheaf : S.Etaleᵒᵖ ⥤ Type u := (generatorSubfunctor L).toFunctor

include hL in
/-- Being a universal generator is local on the small étale site. -/
theorem isUniversalGenerator_of_covering {U : S.Etale}
    (s : Γ((Scheme.Modules.pullback ((Scheme.Etale.forget S).obj U).hom).obj L, ⊤)) (R : Sieve U)
    (hR : R ∈ S.smallEtaleTopology U)
    (h : ∀ ⦃Z : S.Etale⦄ (a : Z ⟶ U), R a →
      IsUniversalGenerator L (pullbackSectionsMap L ((Scheme.Etale.forget S).map a) s)) :
    IsUniversalGenerator L (T := (Scheme.Etale.forget S).obj U) s := by
  intro V g
  refine bijective_smul_of_covering L hL (pullbackSectionsMap L g s)
    ((Sieve.functorPushforward (Scheme.Etale.forget S) R).pullback g)
    ((Scheme.fpqcTopology.{u}.over S).pullback_stable g
      ((CoverPreserving.of_isContinuous (Scheme.Etale.forget S) S.smallEtaleTopology
        (Scheme.fpqcTopology.{u}.over S)).cover_preserve hR)) ?_
  rintro W k ⟨Z, a, b, ha, hk⟩
  have e : pullbackSectionsMap L k (pullbackSectionsMap L g s) =
      pullbackSectionsMap L b (pullbackSectionsMap L ((Scheme.Etale.forget S).map a) s) := by
    rw [← pullbackSectionsMap_comp_apply, hk, pullbackSectionsMap_comp_apply]
  rw [e]
  exact h a ha b

include hL in
/-- **The universal generators form a sheaf on the small étale site.** The sections of
Tag 03DS form an étale sheaf (Tag 03DT), and being a universal generator is fpqc local by
`Stacks.EtaleGenerators.bijective_smul_of_covering`. -/
theorem isSheaf_generatorPresheaf :
    Presheaf.IsSheaf S.smallEtaleTopology (generatorPresheaf L) := by
  have hF : Presieve.IsSheaf S.smallEtaleTopology (sectionsPresheaf L) :=
    (Scheme.Etale.forget S).op_comp_isSheaf_of_isSheaf_type S.smallEtaleTopology
      ((isSheaf_iff_isSheaf_of_type _ _).1
        (isSheaf_fpqc_quasiCoherentPresheafFunctor_forget L hL))
  rw [isSheaf_iff_isSheaf_of_type, Subfunctor.isSheaf_iff _ hF]
  intro U s hs
  exact isUniversalGenerator_of_covering L hL s _ hs (fun _ a ha => ha)

include hL in
/-- **Local generators exist étale locally**: every étale `S`-scheme is covered by étale
`S`-schemes over which `L` has a universal generator, namely the preimages of the opens of `S`
over which `L` has a generator (an invertible module is locally free of rank one). -/
theorem exists_covering_nonempty_generatorPresheaf (U : S.Etale) :
    ∃ R ∈ S.smallEtaleTopology U, ∀ ⦃V : S.Etale⦄ ⦃f : V ⟶ U⦄, R f →
      Nonempty ((generatorPresheaf L).obj (op V)) := by
  have := Stacks.Cohomology.Generators.isFiniteLocallyFreeOfRank_one_of_isInvertible
    S.toRingedSpace L hL
  choose W hW t using fun x : U.left =>
    Stacks.Cohomology.Generators.exists_generator_section S.toRingedSpace L (U.hom.base x)
  let V (x : U.left) : S.Etale := Scheme.Etale.mk ((U.hom ⁻¹ᵁ W x).ι ≫ U.hom)
  let f (x : U.left) : V x ⟶ U := MorphismProperty.Over.homMk (U.hom ⁻¹ᵁ W x).ι rfl
  have hgen (x : U.left) : Nonempty ((generatorPresheaf L).obj (op (V x))) := by
    obtain ⟨tx⟩ := t x
    have hle : (⊤ : (V x).left.Opens) ≤ (V x).hom ⁻¹ᵁ W x := fun z _ => by
      show U.hom.base ((U.hom ⁻¹ᵁ W x).ι.base z) ∈ W x
      exact z.2
    have g := Stacks.SheafOfModules.generatorRestrict _ hle
      (pullbackGenerator (V x).hom L hL (W x) tx)
    exact ⟨⟨g.val, isUniversalGenerator_of_generatorSections L hL
      (T := (Scheme.Etale.forget S).obj (V x)) g⟩⟩
  refine ⟨Sieve.ofArrows V f, ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, ⟨⟨x, hW x⟩, rfl⟩⟩
  · rintro Z g ⟨Y, a, b, ⟨x⟩, rfl⟩
    obtain ⟨s⟩ := hgen x
    exact ⟨(generatorPresheaf L).map a.op s⟩

/-- The section of `U^*L` underlying a section of the presheaf of generators. -/
def sec {U : S.Etale} (s : (generatorPresheaf L).obj (op U)) :
    Γ((Scheme.Modules.pullback U.hom).obj L, ⊤) :=
  s.1

/-- The restriction maps of the presheaf of generators are the pullback maps of Tag 03DS. -/
theorem sec_map {U V : S.Etale} (f : V ⟶ U) (s : (generatorPresheaf L).obj (op U)) :
    sec L ((generatorPresheaf L).map f.op s) =
      pullbackSectionsMap L ((Scheme.Etale.forget S).map f) (sec L s) :=
  rfl

/-- The action of a global unit on a generator. -/
def unitSmul {U : S.Etale} (a : (Γ(U.left, ⊤))ˣ) (s : (generatorPresheaf L).obj (op U)) :
    (generatorPresheaf L).obj (op U) :=
  ⟨(a : Γ(U.left, ⊤)) • sec L s, IsUniversalGenerator.unit_smul L s.2 a⟩

/-- The section underlying the action of a unit on a generator is the unit times the section. -/
theorem sec_unitSmul {U : S.Etale} (a : (Γ(U.left, ⊤))ˣ) (s : (generatorPresheaf L).obj (op U)) :
    sec L (unitSmul L a s) = (a : Γ(U.left, ⊤)) • sec L s := rfl

/-- Restriction of generators commutes with the action of units. -/
theorem map_unitSmul {U V : S.Etale} (f : V ⟶ U) (a : (Γ(U.left, ⊤))ˣ)
    (s : (generatorPresheaf L).obj (op U)) :
    (generatorPresheaf L).map f.op (unitSmul L a s) =
      unitSmul L (Units.map f.left.appTop.hom a) ((generatorPresheaf L).map f.op s) :=
  Subtype.ext (pullbackSectionsMap_smul L ((Scheme.Etale.forget S).map f) _ (sec L s))

end Stacks.EtaleGenerators

end
