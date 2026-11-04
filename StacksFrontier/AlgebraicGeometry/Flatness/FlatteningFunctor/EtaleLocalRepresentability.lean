module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ImmersionLocalRepresentatives
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.IsoLocusProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningInjective
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ConverseContainmentShrink
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange

/-!
# Étale localization of the isomorphism locus of a module map

Let `f : X ⟶ S` be of finite presentation and let `u : F ⟶ G` be a surjection of quasi-coherent
modules on `X` with `F` of finite presentation, flat over `S` and pure relative to `S`.  The locus
where `u` becomes an isomorphism after base change — the functor
`Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor` — is represented by a closed
immersion into `S`.  This is the first assertion of Tag 05PF, and the devissage of the source's
proof is carried out here.

## The devissage

Around a point `s` of the base, purity of `F` along the fibre `X_s` produces (Tags 05KW, 05L4,
05KR and 05LW, packaged as
`AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong`) an affine
elementary étale neighbourhood `S' ⟶ S` of `s`, an affine chart `X' ⟶ X` étale over `X` whose
module of sections is projective over `Γ(S', 𝒪_{S'})`, and an affine open `W₀ ∋ s'` of `S'` over
every point of which the associated points of the fibres of `F ×_S S'` lie in the image of
`X' ⟶ X ×_S S'`.

That containment of associated points is exactly the hypothesis under which Tag 05PD makes the
unit `F ⟶ (X' ⟶ X)_* (X' ⟶ X)^* F` a monomorphism, hence under which `u` is an isomorphism
precisely when its restriction to `X'` is: the isomorphism locus of `u` over `W₀` agrees with the
isomorphism locus of `u|_{X'}`.  The latter is an affine situation with projective sections, where
the locus is cut out by the flattening ideal of Tag 05PE —
`Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion_of_projective_sections`.

So the functor is representable by a closed immersion after an étale base change around every
point of `S`.  Such base changes form an fpqc covering, and the functor is an fpqc sheaf (Tag
05MJ), so the local representatives glue: their pairwise comparison isomorphisms are forced by
the functor being subterminal, which turns them into a descent datum for schemes (Tag 023W) whose
members are closed immersions, and that datum is effective by Tag 03I0 — effective descent for
affine morphisms along an fpqc covering indexed in the universe of the schemes, Tag 0245, in the
form `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom`.

## Main results

* `Stacks.Flatness.isomorphismFunctor_representableBy_closedImmersion`: the first assertion of
  Tag 05PF.

## Implementation notes

The covering of `S` by étale neighbourhoods is indexed by the points of `S`, a type in the
universe of the schemes; this is what makes Tag 0245 available, since the library's effective
descent for affine morphisms is proved for a family indexed in that universe.

Because `isomorphismFunctor` is subterminal, a representability datum is determined by a
bijection of `Nonempty`s, which is what
`Stacks.Flatness.ModuleMapBaseChangeSituation.representableByOfNonemptyIff` records.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 03I0](https://stacks.math.columbia.edu/tag/03I0)
* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
* [Stacks Project, Tag 05PD](https://stacks.math.columbia.edu/tag/05PD)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- The pullback of a sheaf of modules of finite presentation along a morphism of schemes is of
finite presentation.  This is Tag 01BQ for ringed spaces, read on schemes. -/
theorem isFinitePresentation_pullback_obj {A B : Scheme.{u}} (v : A ⟶ B) (G : B.Modules)
    [G.IsFinitePresentation] : ((Scheme.Modules.pullback v).obj G).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation A.toRingedSpace B.toRingedSpace
    v.toLRSHom.toShHom G (show G.IsFinitePresentation from inferInstance)

/-- A morphism is a monomorphism as soon as its image under a left adjoint is one and the unit of
the adjunction is a monomorphism at its source. -/
private theorem mono_of_mono_unit_of_mono_map {C E : Type*} [Category C] [Category E]
    {L : C ⥤ E} {R : E ⥤ C} (adj : L ⊣ R) {M N : C} (φ : M ⟶ N)
    [Mono (adj.unit.app M)] [Mono (L.map φ)] : Mono φ := by
  let _ := adj.isRightAdjoint
  have : Mono (adj.unit.app M ≫ R.map (L.map φ)) := inferInstance
  exact mono_of_mono_fac (h := adj.unit.app M ≫ R.map (L.map φ)) (adj.unit.naturality φ)

/-- **An epimorphism of modules is an isomorphism exactly when its inverse image is**, provided
the unit of the inverse-image/direct-image adjunction is a monomorphism at its source: the
inverse image is then faithful enough to detect injectivity. -/
private theorem isIso_iff_isIso_pullback_of_mono_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    {F G : X.Modules} (φ : F ⟶ G) [Epi φ]
    [Mono ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app F)] :
    IsIso φ ↔ IsIso ((Scheme.Modules.pullback g).map φ) := by
  refine ⟨fun _ ↦ Functor.map_isIso _ _, fun h ↦ ?_⟩
  have := h
  have : Mono φ :=
    mono_of_mono_unit_of_mono_map (Scheme.Modules.pullbackPushforwardAdjunction g) φ
  exact isIso_of_mono_of_epi φ

/-- **Stacks Project, Tag 05PD read as a criterion.**  A surjection out of a module flat over the
base becomes an isomorphism exactly when it does after restriction along a flat morphism whose
image contains the relative assassin. -/
private theorem isIso_iff_isIso_pullback_of_relativeAssassin_subset_range
    {X' X S : Scheme.{u}} (f : X ⟶ S) (g : X' ⟶ X) [LocallyOfFiniteType f] [Flat g]
    {F G : X.Modules} [F.IsQuasicoherent] [F.IsFiniteType] (φ : F ⟶ G) [Epi φ]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hAss : Stacks.Divisors.relativeAssassin f F ⊆ Set.range g.base) :
    IsIso φ ↔ IsIso ((Scheme.Modules.pullback g).map φ) := by
  have := mono_pullbackPushforwardUnit_of_relativeAssassin_subset_range f g F hflat hAss
  exact isIso_iff_isIso_pullback_of_mono_unit g φ

/-- Projectivity of the global sections over an external base transports along an isomorphism of
modules on the source. -/
private theorem projective_sections_of_iso_overBase {Y T : Scheme.{u}} (q : Y ⟶ T)
    {M N : Y.Modules} (e : M ≅ N)
    (hM : letI : Module Γ(T, ⊤) Γ(M, ⊤) := Module.compHom Γ(M, ⊤) q.appTop.hom
      Module.Projective Γ(T, ⊤) Γ(M, ⊤)) :
    letI : Module Γ(T, ⊤) Γ(N, ⊤) := Module.compHom Γ(N, ⊤) q.appTop.hom
    Module.Projective Γ(T, ⊤) Γ(N, ⊤) := by
  let _ : Module Γ(T, ⊤) Γ(M, ⊤) := Module.compHom Γ(M, ⊤) q.appTop.hom
  let _ : Module Γ(T, ⊤) Γ(N, ⊤) := Module.compHom Γ(N, ⊤) q.appTop.hom
  let _ : Module.Projective Γ(T, ⊤) Γ(M, ⊤) := hM
  let eV := asIso (e.hom.app ⊤)
  let eLin : Γ(M, ⊤) ≃ₗ[Γ(T, ⊤)] Γ(N, ⊤) :=
    { toFun := eV.hom.hom
      invFun := eV.inv.hom
      left_inv := fun x ↦ by simp
      right_inv := fun x ↦ by simp
      map_add' := fun x y ↦ map_add eV.hom.hom x y
      map_smul' := fun r x ↦ Scheme.Modules.Hom.app_smul e.hom (q.appTop.hom r) x }
  exact Module.Projective.of_equiv' eLin

end AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.isQuasicoherent_pullback_obj
  AlgebraicGeometry.isFinitePresentation_pullback_obj

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- The situation obtained by base change along a scheme over the base. -/
private noncomputable abbrev baseChangeSituation (D : ModuleMapBaseChangeSituation.{u})
    (T : Over D.S) : ModuleMapBaseChangeSituation.{u} where
  S := T.left
  X := pullback D.f T.hom
  f := pullback.snd D.f T.hom
  F := (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F
  G := (Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.G
  hom := D.baseChangeMap T
  isQuasicoherentF := AlgebraicGeometry.isQuasicoherent_pullback_obj _ _
  isQuasicoherentG := AlgebraicGeometry.isQuasicoherent_pullback_obj _ _

/-- The situation obtained by restricting the source along a morphism into it. -/
private noncomputable abbrev sourceChangeSituation (D : ModuleMapBaseChangeSituation.{u})
    {X' : Scheme.{u}} (g : X' ⟶ D.X) : ModuleMapBaseChangeSituation.{u} where
  S := D.S
  X := X'
  f := g ≫ D.f
  F := (Scheme.Modules.pullback g).obj D.F
  G := (Scheme.Modules.pullback g).obj D.G
  hom := (Scheme.Modules.pullback g).map D.hom

/-- The source module of a base-changed situation is flat over the new base. -/
private theorem isFlatOver_baseChangeSituation (D : ModuleMapBaseChangeSituation.{u})
    (T : Over D.S) (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F) :
    IsFlatOver (baseChangeSituation D T).f.toLRSHom.toShHom (baseChangeSituation D T).F :=
  @AlgebraicGeometry.modulePullback_isFlatOver _ _ _ _ _ _ _ _
    (IsPullback.of_hasPullback D.f T.hom) D.F D.isQuasicoherentF hflat

/-- Invertibility of a homomorphism of modules is unchanged by inverse image along an
isomorphism. -/
private theorem isIso_pullback_map_iff_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) {F G : Y.Modules}
    (φ : F ⟶ G) : IsIso ((Scheme.Modules.pullback e.hom).map φ) ↔ IsIso φ := by
  refine ⟨fun h ↦ ?_, fun _ ↦ Functor.map_isIso _ _⟩
  have := h
  have hi : IsIso ((Scheme.Modules.pullback e.inv).map
      ((Scheme.Modules.pullback e.hom).map φ)) := inferInstance
  exact (NatIso.isIso_map_iff ((Scheme.Modules.pullbackComp e.inv e.hom) ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id) ≪≫ (Scheme.Modules.pullbackId Y)) φ).mp hi

/-- Base changing the situation and then testing on a scheme over the new base is testing on the
same scheme over the original base: the two iterated fibre products agree. -/
private theorem isIsomorphismAfterBaseChange_baseChangeSituation_iff
    (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) (V : Over T.left) :
    (baseChangeSituation D T).IsIsomorphismAfterBaseChange V ↔
      D.IsIsomorphismAfterBaseChange ((Over.map T.hom).obj V) := by
  let h := (IsPullback.of_hasPullback (pullback.snd D.f T.hom) V.hom).paste_horiz
    (IsPullback.of_hasPullback D.f T.hom)
  let e := h.isoPullback
  let ε := (Scheme.Modules.pullbackComp
      (pullback.fst (pullback.snd D.f T.hom) V.hom) (pullback.fst D.f T.hom)) ≪≫
    (Scheme.Modules.pullbackCongr h.isoPullback_hom_fst.symm) ≪≫
    (Scheme.Modules.pullbackComp e.hom (pullback.fst D.f (V.hom ≫ T.hom))).symm
  exact (NatIso.isIso_map_iff ε D.hom).trans
    (isIso_pullback_map_iff_of_iso e
      ((Scheme.Modules.pullback (pullback.fst D.f (V.hom ≫ T.hom))).map D.hom))

/-- Two subterminal presheaves on a category are isomorphic when they have sections over the same
objects. -/
private noncomputable def iso_of_nonempty_iff {C : Type*} [Category C] (F G : Cᵒᵖ ⥤ Type)
    [∀ X, Subsingleton (F.obj X)] [∀ X, Subsingleton (G.obj X)]
    (h : ∀ X, Nonempty (F.obj (op X)) ↔ Nonempty (G.obj (op X))) : F ≅ G :=
  NatIso.ofComponents (fun X ↦ Equiv.toIso
    { toFun := fun x ↦ Classical.choice ((h X.unop).mp ⟨x⟩)
      invFun := fun x ↦ Classical.choice ((h X.unop).mpr ⟨x⟩)
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }) fun _ ↦ by
    ext
    exact Subsingleton.elim _ _

/-- Base changing twice is base changing once along the composite. -/
private noncomputable def isomorphismFunctorIteratedBaseChangeIso
    (D : ModuleMapBaseChangeSituation.{u}) (T : Over D.S) (V : Over T.left) :
    (baseChangeSituation (baseChangeSituation D T) V).isomorphismFunctor ≅
      (baseChangeSituation D ((Over.map T.hom).obj V)).isomorphismFunctor := by
  have heq (Q : Over V.left) :
      (baseChangeSituation (baseChangeSituation D T) V).IsIsomorphismAfterBaseChange Q ↔
      (baseChangeSituation D ((Over.map T.hom).obj V)).IsIsomorphismAfterBaseChange Q := by
    rw [isIsomorphismAfterBaseChange_baseChangeSituation_iff,
      isIsomorphismAfterBaseChange_baseChangeSituation_iff,
      isIsomorphismAfterBaseChange_baseChangeSituation_iff]
    change D.IsIsomorphismAfterBaseChange (Over.mk ((Q.hom ≫ V.hom) ≫ T.hom)) ↔
      D.IsIsomorphismAfterBaseChange (Over.mk (Q.hom ≫ V.hom ≫ T.hom))
    rw [Category.assoc]
  exact iso_of_nonempty_iff _ _ fun Q ↦
    by
    rw [isomorphismFunctor_obj_nonempty_iff, isomorphismFunctor_obj_nonempty_iff]
    exact heq Q

/-- A subterminal functor is represented by an object whose morphisms from each source form a
subsingleton as soon as the two are inhabited together. -/
private noncomputable def representableByOfNonemptyIff {C : Type*} [Category C]
    (F : Cᵒᵖ ⥤ Type*) (Y : C) (hF : ∀ X, Subsingleton (F.obj (op X)))
    (hHom : ∀ X, Subsingleton (X ⟶ Y))
    (h : ∀ X, Nonempty (F.obj (op X)) ↔ Nonempty (X ⟶ Y)) : F.RepresentableBy Y := by
  classical
  refine ⟨?_, ?_⟩
  · intro X
    exact
      { toFun := fun g ↦ Classical.choice ((h X).2 ⟨g⟩)
        invFun := fun x ↦ Classical.choice ((h X).1 ⟨x⟩)
        left_inv := fun _ ↦ Subsingleton.elim _ _
        right_inv := fun _ ↦ Subsingleton.elim _ _ }
  · intro X X' a b
    exact @Subsingleton.elim (F.obj (op X)) (hF X) _ _

/-- A representative of the isomorphism functor of a situation base changes to a representative
of the isomorphism functor of the base-changed situation. -/
private theorem exists_representation_baseChangeSituation
    (D : ModuleMapBaseChangeSituation.{u}) (W : Over D.S) [IsClosedImmersion W.hom]
    (r : D.isomorphismFunctor.RepresentableBy W) (T : Over D.S) :
    ∃ Z : Over T.left, IsClosedImmersion Z.hom ∧
      Nonempty ((baseChangeSituation D T).isomorphismFunctor.RepresentableBy Z) := by
  let Z := (Over.pullback T.hom).obj W
  have : IsClosedImmersion Z.hom :=
    inferInstanceAs (IsClosedImmersion (pullback.snd W.hom T.hom))
  refine ⟨Z, inferInstance, ⟨representableByOfNonemptyIff
    (baseChangeSituation D T).isomorphismFunctor Z (fun V ↦ inferInstance)
    (fun V ↦ subsingleton_overHom_of_mono V Z) fun V ↦ ?_⟩⟩
  show Nonempty (PLift ((baseChangeSituation D T).IsIsomorphismAfterBaseChange V)) ↔ _
  rw [nonempty_plift, nonempty_prop, isIsomorphismAfterBaseChange_baseChangeSituation_iff]
  let adj := Over.mapPullbackAdj T.hom
  exact ⟨fun h ↦ ⟨adj.homEquiv _ _ (r.homEquiv.symm ⟨h⟩)⟩,
    fun ⟨g⟩ ↦ (r.homEquiv ((adj.homEquiv _ _).symm g)).down⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- A scheme over a member of the family making `u` an isomorphism lifts, over the base, to the
local representative there. -/
private theorem exists_lift_of_localRepresentative (D : ModuleMapBaseChangeSituation.{u})
    {U : Scheme.{u}} (q : U ⟶ D.S) (W : Over U)
    (h : ∀ V : Over U, D.IsIsomorphismAfterBaseChange ((Over.map q).obj V) ↔ Nonempty (V ⟶ W))
    {T : Over D.S} (a : T ⟶ Over.mk q) (hT : D.IsIsomorphismAfterBaseChange T) :
    ∃ b : T ⟶ (Over.map q).obj W, b ≫ AlgebraicGeometry.structureMap q W = a := by
  let V := Over.mk a.left
  let e : (Over.map q).obj V ≅ T := Over.isoMk (Iso.refl _) (by simpa [V] using (Over.w a).symm)
  obtain ⟨b⟩ := (h V).mp (D.isIsomorphismAfterBaseChange_of_hom e.hom hT)
  refine ⟨Over.homMk b.left ?_, Over.OverMorphism.ext (Over.w b)⟩
  show b.left ≫ W.hom ≫ q = T.hom
  rw [← Category.assoc, Over.w b]
  exact Over.w a

variable (D : ModuleMapBaseChangeSituation.{u}) {U V : Scheme.{u}} (q : U ⟶ D.S) (r : V ⟶ D.S)
  (W : Over U) (Z : Over V)

/-- The comparison morphism between two local representatives over the pairwise fibre product of
the base changes: it exists because the first factor makes `u` an isomorphism, hence factors
through the second representative. -/
private noncomputable def localRepresentativeTransition
    (hW : D.IsIsomorphismAfterBaseChange ((Over.map q).obj W))
    (hZ : ∀ T : Over V, D.IsIsomorphismAfterBaseChange ((Over.map r).obj T) ↔
      Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk q ⨯ (Over.map r).obj Z :=
  prod.lift (prod.fst ≫ AlgebraicGeometry.structureMap q W)
    (Classical.choose (exists_lift_of_localRepresentative D r Z hZ prod.snd
      (D.isIsomorphismAfterBaseChange_of_hom prod.fst hW)))

private theorem localRepresentativeTransition_fst
    (hW : D.IsIsomorphismAfterBaseChange ((Over.map q).obj W))
    (hZ : ∀ T : Over V, D.IsIsomorphismAfterBaseChange ((Over.map r).obj T) ↔
      Nonempty (T ⟶ Z)) :
    localRepresentativeTransition D q r W Z hW hZ ≫ prod.fst =
      prod.fst ≫ AlgebraicGeometry.structureMap q W := by
  simp [localRepresentativeTransition]

private theorem localRepresentativeTransition_snd
    (hW : D.IsIsomorphismAfterBaseChange ((Over.map q).obj W))
    (hZ : ∀ T : Over V, D.IsIsomorphismAfterBaseChange ((Over.map r).obj T) ↔
      Nonempty (T ⟶ Z)) :
    localRepresentativeTransition D q r W Z hW hZ ≫ prod.snd ≫
      AlgebraicGeometry.structureMap r Z = prod.snd := by
  simpa [localRepresentativeTransition] using
    Classical.choose_spec (exists_lift_of_localRepresentative D r Z hZ
      (prod.snd : (Over.map q).obj W ⨯ Over.mk r ⟶ Over.mk r)
      (D.isIsomorphismAfterBaseChange_of_hom prod.fst hW))

attribute [local simp] localRepresentativeTransition_fst localRepresentativeTransition_snd

attribute [local instance] mono_structureMap

/-- The comparison morphism of two local representatives is an isomorphism: both composites are
morphisms into an object with a monomorphic structure map, so they are forced. -/
private noncomputable def localRepresentativeTransitionIso [Mono W.hom] [Mono Z.hom]
    (hW : ∀ T : Over U, D.IsIsomorphismAfterBaseChange ((Over.map q).obj T) ↔ Nonempty (T ⟶ W))
    (hZ : ∀ T : Over V, D.IsIsomorphismAfterBaseChange ((Over.map r).obj T) ↔
      Nonempty (T ⟶ Z)) :
    (Over.map q).obj W ⨯ Over.mk r ≅ Over.mk q ⨯ (Over.map r).obj Z where
  hom := localRepresentativeTransition D q r W Z ((hW W).mpr ⟨𝟙 W⟩) hZ
  inv := (prod.braiding _ _).hom ≫
    localRepresentativeTransition D r q Z W ((hZ Z).mpr ⟨𝟙 Z⟩) hW ≫ (prod.braiding _ _).hom
  hom_inv_id := by
    have := mono_structureMap q W
    refine prod.hom_ext ?_ ?_
    · refine (cancel_mono (AlgebraicGeometry.structureMap q W)).mp ?_
      simp [localRepresentativeTransition_fst, localRepresentativeTransition_snd]
    · simp [localRepresentativeTransition_fst, localRepresentativeTransition_snd]
  inv_hom_id := by
    have := mono_structureMap r Z
    refine prod.hom_ext ?_ ?_
    · simp [localRepresentativeTransition_fst, localRepresentativeTransition_snd]
    · refine (cancel_mono (AlgebraicGeometry.structureMap r Z)).mp ?_
      simp [localRepresentativeTransition_fst, localRepresentativeTransition_snd]

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

variable (D : ModuleMapBaseChangeSituation.{u}) {I : Type u} {U : I → Scheme.{u}}
  (q : ∀ i, U i ⟶ D.S) (W : ∀ i, Over (U i))

/-- **The local representatives form a descent datum.**  The gluing isomorphisms are the
comparison morphisms, and both the compatibility with the projections and the cocycle condition
hold because the functor is subterminal: any two morphisms into a local representative over the
same base agree. -/
private noncomputable def localRepresentativeDescentData [∀ i, Mono (W i).hom]
    (h : ∀ i, ∀ T : Over (U i),
      D.IsIsomorphismAfterBaseChange ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    AlgebraicGeometry.DescentData q where
  obj := W
  gluing i j := Over.isoMk
    (localRepresentativeTransitionIso D (q i) (q j) (W i) (W j) (h i) (h j)) (by
      refine prod.hom_ext ?_ ?_ <;>
        simp [localRepresentativeTransitionIso, localRepresentativeTransition_fst,
          localRepresentativeTransition_snd])
  cocycle i j k := by
    change prod.map (localRepresentativeTransition D (q i) (q j) (W i) (W j)
      ((h i (W i)).mpr ⟨𝟙 _⟩) (h j)) (𝟙 _) ≫
      prodMapLastTwo (localRepresentativeTransition D (q j) (q k) (W j) (W k)
        ((h j (W j)).mpr ⟨𝟙 _⟩) (h k)) =
      prodMapFirstThird (localRepresentativeTransition D (q i) (q k) (W i) (W k)
        ((h i (W i)).mpr ⟨𝟙 _⟩) (h k))
    have := mono_structureMap (q k) (W k)
    refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_
    · simp [prodMapLastTwo, prodMapFirstThird, localRepresentativeTransition_fst,
        localRepresentativeTransition_snd]
    · simp [prodMapLastTwo, prodMapFirstThird, localRepresentativeTransition_fst,
        localRepresentativeTransition_snd]
    · refine (cancel_mono (AlgebraicGeometry.structureMap (q k) (W k))).mp ?_
      simp [prodMapLastTwo, prodMapFirstThird, localRepresentativeTransition_fst,
        localRepresentativeTransition_snd]

/-- **Local representatives by closed immersions glue.**  Their descent datum is effective by Tag
03I0, whose input — effective descent for affine morphisms along an fpqc covering, Tag 0245 — is
available because a closed immersion is affine and the family is indexed in the universe of the
schemes.  Being a closed immersion is local at the target, so the glued scheme is a closed
subscheme of the base. -/
private theorem exists_closedImmersion_of_localRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage D.S) [∀ i, IsClosedImmersion (W i).hom]
    (h : ∀ i, ∀ T : Over (U i),
      D.IsIsomorphismAfterBaseChange ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    ∃ Z : Over D.S, IsClosedImmersion Z.hom ∧
      ∀ i, Nonempty ((Over.pullback (q i)).obj Z ≅ W i) := by
  let d := localRepresentativeDescentData D q W h
  obtain ⟨Z, ⟨e⟩⟩ := AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom q hq d
    fun i ↦ inferInstanceAs (IsAffineHom (W i).hom)
  let ei (i : I) : (Over.pullback (q i)).obj Z ≅ W i :=
    (eqToIso ((AlgebraicGeometry.canonicalFamilyDescentFunctor q).obj Z i)).symm ≪≫
      (AlgebraicGeometry.DescentData.evaluation i).mapIso e
  refine ⟨Z, ?_, fun i ↦ ⟨ei i⟩⟩
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := @IsClosedImmersion) hq ?_
  rintro V' g' _ ⟨i⟩
  have : IsIso (ei i).hom.left := Functor.map_isIso (Over.forget (U i)) (ei i).hom
  have hw := Over.w (ei i).hom
  change (ei i).hom.left ≫ (W i).hom = pullback.snd Z.hom (q i) at hw
  rw [← hw]
  infer_instance

/-- **A scheme restricting to the local representatives represents the functor.**  The
isomorphism functor is an fpqc sheaf (Tag 05MJ) and so is the functor of points of the candidate,
and the two are inhabited together over each member of the covering family. -/
private theorem representableBy_of_fpqcLocalRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage D.S)
    (h : ∀ i, ∀ T : Over (U i),
      D.IsIsomorphismAfterBaseChange ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i))
    (Z : Over D.S) [Mono Z.hom] (e : ∀ i, (Over.pullback (q i)).obj Z ≅ W i) :
    Nonempty (D.isomorphismFunctor.RepresentableBy Z) := by
  classical
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp D.isomorphismFunctor_isSheaf_fpqc
  have hZ : Presieve.IsSheaf (Scheme.fpqcTopology.over D.S) (yoneda.obj Z) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  refine ⟨representableByOfNonemptyIff D.isomorphismFunctor Z (fun T ↦ inferInstance)
    (fun T ↦ subsingleton_overHom_of_mono T Z) fun T ↦ ?_⟩
  let Q (i : I) := (Over.map (q i)).obj ((Over.pullback (q i)).obj T)
  let a (i : I) : Q i ⟶ T := overBaseChangeProjection (q i) T
  have ha : Sieve.ofArrows Q a ∈ (Scheme.fpqcTopology.over D.S) T :=
    overBaseChangeProjection_covering q hq T
  rw [nonempty_iff_forall_of_subsingleton_sheaf D.isomorphismFunctor hF
      (fun T ↦ inferInstance) Q a ha,
    show Nonempty (T ⟶ Z) ↔ ∀ i, Nonempty (Q i ⟶ Z) from
      nonempty_iff_forall_of_subsingleton_sheaf (yoneda.obj Z) hZ
        (fun T' ↦ subsingleton_overHom_of_mono T' Z) Q a ha]
  refine forall_congr' fun i ↦ ?_
  show Nonempty (PLift (D.IsIsomorphismAfterBaseChange (Q i))) ↔ Nonempty (Q i ⟶ Z)
  rw [nonempty_plift, nonempty_prop, h i ((Over.pullback (q i)).obj T)]
  let adj := Over.mapPullbackAdj (q i)
  exact ⟨fun ⟨g⟩ ↦ ⟨(adj.homEquiv _ _).symm (g ≫ (e i).inv)⟩,
    fun ⟨g⟩ ↦ ⟨adj.homEquiv _ _ g ≫ (e i).hom⟩⟩

/-- Local representability by closed immersions along an fpqc covering of the base gives global
representability by a closed immersion. -/
private theorem exists_representation_of_fpqcLocalRepresentatives
    (hq : Presieve.ofArrows U q ∈ Scheme.fpqcPrecoverage D.S) [∀ i, IsClosedImmersion (W i).hom]
    (h : ∀ i, ∀ T : Over (U i),
      D.IsIsomorphismAfterBaseChange ((Over.map (q i)).obj T) ↔ Nonempty (T ⟶ W i)) :
    ∃ Z : Over D.S, IsClosedImmersion Z.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy Z) := by
  classical
  obtain ⟨Z, hZ, e⟩ := exists_closedImmersion_of_localRepresentatives D q W hq h
  have := hZ
  exact ⟨Z, hZ, representableBy_of_fpqcLocalRepresentatives D q W hq h Z
    fun i ↦ Classical.choice (e i)⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- **Étale-local representability suffices.**  Étale neighbourhoods of all the points of the
base form an fpqc covering, so representatives over them glue. -/
private theorem exists_representation_of_etaleLocalRepresentation
    (D : ModuleMapBaseChangeSituation.{u})
    (hlocal : ∀ s : D.S, ∃ N : AlgebraicGeometry.EtaleNeighborhood D.S s,
      ∃ W : Over N.scheme, IsClosedImmersion W.hom ∧
        Nonempty
          ((baseChangeSituation D (Over.mk N.toBase)).isomorphismFunctor.RepresentableBy W)) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) := by
  classical
  choose N W hclosed hrepr using hlocal
  have (s : D.S) : IsClosedImmersion (W s).hom := hclosed s
  have hcover : Presieve.ofArrows (fun s ↦ (N s).scheme) (fun s ↦ (N s).toBase) ∈
      Scheme.fpqcPrecoverage D.S := by
    refine Scheme.fppfPrecoverage_le_fpqcPrecoverage _ ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun s ↦ ⟨s, (N s).point, (N s).map_point⟩, fun s ↦ ⟨inferInstance, inferInstance⟩⟩)
  refine exists_representation_of_fpqcLocalRepresentatives D (fun s ↦ (N s).toBase) W hcover
    fun s T ↦ ?_
  let rs := Classical.choice (hrepr s)
  refine (isIsomorphismAfterBaseChange_baseChangeSituation_iff D
    (Over.mk (N s).toBase) T).symm.trans ?_
  exact ⟨fun hh ↦ ⟨rs.homEquiv.symm ⟨hh⟩⟩, fun ⟨g⟩ ↦ (rs.homEquiv g).down⟩

/-- **Restricting the source along a flat chart does not change the isomorphism locus over an
open of the base whose fibrewise associated points lie in the chart.**  This is Tag 05PD. -/
private theorem isIso_sourceChange_iff_of_relativeAssassin_over_range
    (D : ModuleMapBaseChangeSituation.{u}) [LocallyOfFiniteType D.f] [D.F.IsFinitePresentation]
    [Epi D.hom] {X' : Scheme.{u}} (g : X' ⟶ D.X) [Flat g]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F) (T : Over D.S)
    (hAss : ∀ x ∈ Stacks.Divisors.relativeAssassin D.f D.F,
      D.f.base x ∈ Set.range T.hom.base → x ∈ Set.range g.base) :
    D.IsIsomorphismAfterBaseChange T ↔
      (sourceChangeSituation D g).IsIsomorphismAfterBaseChange T := by
  let k := AlgebraicGeometry.compBaseChangeMap D.f g T.hom
  have hk := (AlgebraicGeometry.isPullback_baseChangeMap D.f g T.hom).flip
  have : Flat k := AlgebraicGeometry.flat_baseChangeMap D.f g T.hom
  have hAss' : Stacks.Divisors.relativeAssassin (pullback.snd D.f T.hom)
      ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F) ⊆ Set.range k.base := by
    intro x hx
    have hx' := ((AlgebraicGeometry.mem_relativeAssassin_pullback_iff D.f T.hom D.F x).mp hx).1
    have hbase : D.f.base (pullback.fst D.f T.hom x) ∈ Set.range T.hom.base :=
      ⟨pullback.snd D.f T.hom x, (congrArg (fun z : pullback D.f T.hom ⟶ D.S => z.base x)
        (pullback.condition (f := D.f) (g := T.hom))).symm⟩
    obtain ⟨y, hy⟩ := hAss _ hx' hbase
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback hk y x hy
    exact ⟨z, hz⟩
  have : Epi (D.baseChangeMap T) :=
    inferInstanceAs (Epi ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).map D.hom))
  have : ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F).IsFinitePresentation :=
    AlgebraicGeometry.isFinitePresentation_pullback_obj _ _
  have : ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F).IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation
      ((Scheme.Modules.pullback (pullback.fst D.f T.hom)).obj D.F)
  have hkfst : k ≫ pullback.fst D.f T.hom = pullback.fst (g ≫ D.f) T.hom ≫ g :=
    pullback.lift_fst _ _ _
  let e := (Scheme.Modules.pullbackComp k (pullback.fst D.f T.hom)) ≪≫
    (Scheme.Modules.pullbackCongr hkfst) ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst (g ≫ D.f) T.hom) g).symm
  exact (AlgebraicGeometry.isIso_iff_isIso_pullback_of_relativeAssassin_subset_range
    (pullback.snd D.f T.hom) k (D.baseChangeMap T)
      (isFlatOver_baseChangeSituation D T hflat) hAss').trans (NatIso.isIso_map_iff e D.hom)

/-- A representative of the isomorphism functor of the source-restricted situation represents the
isomorphism functor of the situation base changed to an open over which the fibrewise associated
points lie in the chart. -/
private theorem exists_representation_on_open_of_sourceChange
    (D : ModuleMapBaseChangeSituation.{u}) [LocallyOfFiniteType D.f] [D.F.IsFinitePresentation]
    [Epi D.hom] {X' : Scheme.{u}} (g : X' ⟶ D.X) [Flat g]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F) (V : D.S.Opens)
    (hAss : ∀ x ∈ Stacks.Divisors.relativeAssassin D.f D.F,
      D.f.base x ∈ V → x ∈ Set.range g.base)
    (W : Over D.S) [IsClosedImmersion W.hom]
    (r : (sourceChangeSituation D g).isomorphismFunctor.RepresentableBy W) :
    ∃ Z : Over V.toScheme, IsClosedImmersion Z.hom ∧
      Nonempty ((baseChangeSituation D (Over.mk V.ι)).isomorphismFunctor.RepresentableBy Z) := by
  obtain ⟨Z, hZ, ⟨rZ⟩⟩ :=
    exists_representation_baseChangeSituation (sourceChangeSituation D g) W r (Over.mk V.ι)
  have heq (T : Over V.toScheme) :
      (baseChangeSituation D (Over.mk V.ι)).IsIsomorphismAfterBaseChange T ↔
      (baseChangeSituation (sourceChangeSituation D g)
        (Over.mk V.ι)).IsIsomorphismAfterBaseChange T := by
    rw [isIsomorphismAfterBaseChange_baseChangeSituation_iff,
      isIsomorphismAfterBaseChange_baseChangeSituation_iff]
    refine isIso_sourceChange_iff_of_relativeAssassin_over_range D g hflat _ fun x hx hbase ↦ ?_
    obtain ⟨t, ht⟩ := hbase
    exact hAss x hx (ht ▸ (T.hom.base t).property)
  refine ⟨Z, hZ, ⟨rZ.ofIso (iso_of_nonempty_iff _ _ fun T ↦ ?_).symm⟩⟩
  rw [isomorphismFunctor_obj_nonempty_iff, isomorphismFunctor_obj_nonempty_iff]
  exact heq T

/-- **Representability over an étale neighbourhood of a point of the base.**  Purity of `F` along
the fibre over `s` yields, by Tags 05KW, 05L4, 05KR and 05LW, an affine elementary étale
neighbourhood of `s`, an affine chart of `X` étale over it with projective sections, and an affine
open of the neighbourhood over which the fibrewise associated points lie in that chart.  Over that
open the isomorphism locus of `u` agrees with the isomorphism locus of its restriction to the
chart (Tag 05PD), which is an affine situation with projective sections and so is cut out by a
closed subscheme (Tag 05PE). -/
private theorem exists_etaleLocalRepresentation (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [Epi D.hom]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (hpure : AlgebraicGeometry.IsPureRelative D.f D.F) (s : D.S) :
    ∃ N : AlgebraicGeometry.EtaleNeighborhood D.S s,
      ∃ W : Over N.scheme, IsClosedImmersion W.hom ∧
        Nonempty
          ((baseChangeSituation D (Over.mk N.toBase)).isomorphismFunctor.RepresentableBy W) := by
  obtain ⟨U, X', p, g, hcomm, hUa, hXa, hgE, -, -, hproj, WO, -, hWOmem, hWOsub⟩ :=
    AlgebraicGeometry.exists_chart_affineOpen_fibrewiseContainment_of_isPureAlong D.f D.F s
      (fun x ↦ hflat (D.f.fiberι s x)) (hpure s)
  have : IsAffine U.scheme := hUa
  have : IsAffine X' := hXa
  have : Etale g := hgE
  let DU := baseChangeSituation D (Over.mk U.toBase)
  let k : X' ⟶ DU.X := pullback.lift g p hcomm
  have : Etale k := AlgebraicGeometry.etale_pullback_lift_of_etale D.f U.toBase g p hcomm
  have : LocallyOfFinitePresentation DU.f :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd D.f U.toBase))
  have : QuasiCompact DU.f := inferInstanceAs (QuasiCompact (pullback.snd D.f U.toBase))
  have : DU.F.IsFinitePresentation := AlgebraicGeometry.isFinitePresentation_pullback_obj _ _
  have : Epi DU.hom :=
    inferInstanceAs (Epi ((Scheme.Modules.pullback (pullback.fst D.f U.toBase)).map D.hom))
  have hflatU := isFlatOver_baseChangeSituation D (Over.mk U.toBase) hflat
  let E := sourceChangeSituation DU k
  have : IsAffine E.X := hXa
  have : IsAffine E.S := hUa
  have : Epi E.hom := inferInstanceAs (Epi ((Scheme.Modules.pullback k).map DU.hom))
  -- the chart's sections are projective over the neighbourhood, by transport along `k ≫ DU.f = p`
  have hprojE : let : Module Γ(E.S, ⊤) Γ(E.F, ⊤) := Module.compHom _ E.f.appTop.hom
      Module.Projective Γ(E.S, ⊤) Γ(E.F, ⊤) := by
    show let : Module Γ(U.scheme, ⊤) Γ((Scheme.Modules.pullback k).obj DU.F, ⊤) :=
      Module.compHom _ (k ≫ DU.f).appTop.hom
      Module.Projective Γ(U.scheme, ⊤) Γ((Scheme.Modules.pullback k).obj DU.F, ⊤)
    rw [show k ≫ DU.f = p from pullback.lift_snd _ _ _]
    exact AlgebraicGeometry.projective_sections_of_iso_overBase p
      (((Scheme.Modules.pullbackComp k (pullback.fst D.f U.toBase)) ≪≫
        Scheme.Modules.pullbackCongr (pullback.lift_fst _ _ _)).app D.F).symm hproj
  obtain ⟨W, hW, ⟨rW⟩⟩ :=
    isomorphismFunctor_representableBy_closedImmersion_of_projective_sections E hprojE
  have : IsClosedImmersion W.hom := hW
  -- over `WO` the fibrewise associated points lie in the image of the chart
  have hAss : ∀ x ∈ Stacks.Divisors.relativeAssassin DU.f DU.F,
      DU.f.base x ∈ WO → x ∈ Set.range k.base := by
    intro x hx hxWO
    obtain ⟨t, y, hy, rfl⟩ := (Stacks.Divisors.mem_relativeAssassin _ _ _).mp hx
    exact hWOsub (show t ∈ (WO : Set U.scheme) from
      ((DU.f.range_fiberι t).le ⟨y, rfl⟩ : DU.f.base (DU.f.fiberι t y) = t) ▸ hxWO) hy
  obtain ⟨Z, hZ, ⟨rZ⟩⟩ :=
    exists_representation_on_open_of_sourceChange DU k hflatU WO hAss W rW
  exact ⟨{ scheme := WO.toScheme
           point := ⟨U.point, hWOmem⟩
           toBase := WO.ι ≫ U.toBase
           map_point := U.map_point }, Z, hZ,
    ⟨rZ.ofIso (isomorphismFunctorIteratedBaseChangeIso D (Over.mk U.toBase) (Over.mk WO.ι))⟩⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

namespace Stacks.Flatness

/-- **Stacks Project, Tag 05PF, first assertion.** Let `f : X ⟶ S` be of finite presentation and
let `u : F ⟶ G` be a surjection of quasi-coherent modules on `X` with `F` of finite presentation,
flat over `S` and pure relative to `S`.  Then the locus where `u` becomes an isomorphism after
base change is represented by a closed immersion into `S`.

The source's devissage: purity reduces the question, étale locally on `S`, to an affine situation
whose module of sections is projective, where the locus is cut out by the flattening ideal of Tag
05PE; the étale base changes cover `S` in the fpqc topology and the functor is an fpqc sheaf, so
the local closed subschemes glue. -/
@[stacks 05PF "representability by a closed immersion"]
theorem exists_closedImmersion_representableBy_isomorphismFunctor
    (D : ModuleMapBaseChangeSituation.{u})
    [LocallyOfFinitePresentation D.f] [QuasiCompact D.f] [QuasiSeparated D.f]
    [D.F.IsFinitePresentation] [D.F.IsFiniteType] [Epi D.hom]
    (hflat : IsFlatOver D.f.toLRSHom.toShHom D.F)
    (hpure : AlgebraicGeometry.IsPureRelative D.f D.F) :
    ∃ W : Over D.S, IsClosedImmersion W.hom ∧
      Nonempty (D.isomorphismFunctor.RepresentableBy W) :=
  ModuleMapBaseChangeSituation.exists_representation_of_etaleLocalRepresentation D
    (ModuleMapBaseChangeSituation.exists_etaleLocalRepresentation D hflat hpure)

end Stacks.Flatness

end
