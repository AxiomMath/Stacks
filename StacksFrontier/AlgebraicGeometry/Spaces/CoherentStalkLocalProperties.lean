module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceKernels
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictionStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkIndependenceOfGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportClosedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentFromCoherence

/-!
# Local properties of coherent modules at a geometric point

Let `X` be an algebraic space, `x̄` a geometric point of `X` lying over a point `x` of the
point set of `X`.  A coherent `𝒪_X`-module whose stalk at `x̄` vanishes already vanishes on an
open subspace containing `x`, because the support of a module of finite type is closed; and
injectivity, surjectivity or bijectivity of a map of coherent modules at `x̄` spreads to an
open subspace containing `x`, by applying the vanishing statement to the kernel and to the
cokernel, which are again coherent on the small étale site.

## Main results

* `AlgebraicGeometry.Space.exists_isOpen_isZero_restrictToOpenPoints`: a module of finite type
  with vanishing stalk at a geometric point vanishes near the image of that point.
* `AlgebraicGeometry.Space.exists_isOpen_isZero_restrictToOpenPoints_of_isCoherent`: part (1)
  of Stacks 07UF.
* `AlgebraicGeometry.Space.exists_isOpen_mono_restrictToOpenPoints_map`: part (2).
* `AlgebraicGeometry.Space.exists_isOpen_epi_restrictToOpenPoints_map`: part (3).
* `AlgebraicGeometry.Space.exists_isOpen_isIso_restrictToOpenPoints_map`: part (4).

## Implementation notes

The locally Noetherian hypothesis of the cited lemma is nowhere used: the support of a module of
finite type is closed on any algebraic space, by Stacks 07TZ.  So the four results below are
strict generalisations of the four parts of the lemma.

The open neighbourhood is produced as an open *set of points*, and restriction to it is étale
pullback along the inclusion of the corresponding open subspace,
`AlgebraicGeometry.Space.restrictToOpenPoints`.

The vanishing statement is universe polymorphic in the module sections, but the four parts are
stated with the module sections in the universe `u` of the structure sheaf, because that is the
universe in which cokernels of `𝒪_X`-modules exist, in which étale restriction of modules is
right exact, and in which coherence on the site implies finite type on the site.

## References

* [Stacks Project, Tag 07UF](https://stacks.math.columbia.edu/tag/07UF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ZeroObject

universe u v w m

namespace Stacks.SheafOfModules

section FiniteTypeBridge

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Finitely many sections generating a sheaf of modules over an object `W`, in the sectionwise
sense of `PresheafOfModules.Generates`, generate its restriction to the slice at `W` in the
categorical sense of `SheafOfModules.HasFiniteGlobalGenerators`. -/
@[ega "0 5.1.1" "partial"]
theorem hasFiniteGlobalGenerators_of_generates (M : SheafOfModules.{w} R) {W : C} {n : ℕ}
    (s : Fin n → M.val.obj (op W)) (hs : PresheafOfModules.Generates J M.val s) :
    SheafOfModules.HasFiniteGlobalGenerators (M.over W) := by
  have h1 : HasSheafify (J.over W) AddCommGrpCat.{max u v w} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v w, v, max u v} (J.over W)
  have h2 : (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v w,
      max u v, v} (J.over W)
  refine ⟨n, SheafOfModules.liftPow (R.over W) n, biproduct.ι _, ⟨biproduct.isColimit _⟩,
    SheafOfModules.powDesc (M.over W) (fun i ↦ SheafOfModules.sectionOver M (s i)), ?_⟩
  refine SheafOfModules.epi_powDesc _ _ ?_
  intro V x
  obtain ⟨T, hT, ht⟩ := hs V.left V.hom x
  refine ⟨(Sieve.overEquiv V).symm T, J.overEquiv_symm_mem_over V T hT, ?_⟩
  intro Z g hg
  obtain ⟨a, ha⟩ := ht Z.left g.left hg
  refine ⟨a, ?_⟩
  have hw : (g.left ≫ V.hom) = Z.hom := Over.w g
  change ∑ i, a i • M.val.map Z.hom.op (s i) = M.val.map g.left.op x
  rw [← hw]
  exact ha

/-- **From the sectionwise to the categorical form of Stacks 03DL(5).** A sheaf of modules
whose underlying presheaf of modules is of finite type for `J` is of finite type on the site in
the sense of `SheafOfModules.IsFiniteTypeOnSite`.

The sectionwise condition produces generators only on the members of one family covering the
final object; the categorical condition asks for generators on a covering of *every* object.
The passage is the sieve of objects of that family: an arrow of it has a map into a member of
the family, and generation by finitely many sections is stable under restriction along any
morphism of the site (`PresheafOfModules.Generates.restrict`). -/
theorem isFiniteTypeOnSite_of_presheaf_isFiniteType (M : SheafOfModules.{w} R)
    (h : PresheafOfModules.IsFiniteType J M.val) :
    SheafOfModules.IsFiniteTypeOnSite M := by
  obtain ⟨I, U, hcov, hgen⟩ := h.exists_generators
  refine ⟨fun Z ↦ ?_⟩
  refine ⟨Σ Y : C, {g : Y ⟶ Z // (Sieve.ofObjects U Z).arrows g}, fun p ↦ p.1,
    fun p ↦ p.2.1, ?_, ?_⟩
  · refine J.superset_covering ?_ (hcov Z)
    intro Y g hg
    exact Sieve.ofArrows_mk (fun p : Σ Y : C, {g : Y ⟶ Z // (Sieve.ofObjects U Z).arrows g} ↦ p.1)
      (fun p ↦ p.2.1) ⟨Y, g, hg⟩
  · rintro ⟨Y, g, hg⟩
    obtain ⟨i, ⟨a⟩⟩ := hg
    obtain ⟨n, s, hs⟩ := hgen i
    exact hasFiniteGlobalGenerators_of_generates M _ (hs.restrict a)

end FiniteTypeBridge

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The open subspace cut out by an open set of points -/

/-- The open subspace of an algebraic space cut out by an open set of its points, as an
algebraic space over `S`.  This is the open subspace of Stacks 03BZ attached to the open set. -/
noncomputable def openPointsSubspace (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) : AlgebraicSpaces B S hS :=
  ⟨(openSubspaceOfPoints B S hS X.1 W).toFunctor,
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hW).1⟩

/-- The inclusion of the open subspace cut out by an open set of points. -/
noncomputable def openPointsSubspaceHom (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) : openPointsSubspace B S hS X W hW ⟶ X :=
  ObjectProperty.homMk (openSubspaceOfPoints B S hS X.1 W).ι

/-- The inclusion of an open subspace is étale. -/
theorem isEtale_openPointsSubspaceHom (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) :
    IsEtale B S hS (openPointsSubspaceHom B S hS X W hW).hom :=
  isEtale_of_presheaf_etale B S hS
    (presheaf_etale_of_isOpenImmersion B S hS
      (isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hW).2)

/-- The point set of the open subspace cut out by an open set of points is that set. -/
theorem range_pointsMap_openPointsSubspaceHom (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) :
    Set.range (pointsMap B S hS (openPointsSubspace B S hS X W hW).1
      (openPointsSubspaceHom B S hS X W hW).hom) = W :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS W

/-- Restriction of a module to the open subspace cut out by an open set of points: the étale
pullback along the inclusion, which for an étale morphism is plain restriction of sections. -/
noncomputable def restrictToOpenPoints (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W) :
    Modules.{u, m} B S hS X.1 X.2 ⥤
      Modules.{u, m} B S hS (openPointsSubspace B S hS X W hW).1
        (openPointsSubspace B S hS X W hW).2 :=
  etaleModulePullback.{u, m} B S hS (openPointsSubspaceHom B S hS X W hW)
    (isEtale_openPointsSubspaceHom B S hS X W hW)

/-- A module vanishes on the open subspace cut out by an open set of points disjoint from its
support.  The support of the restriction is the inverse image of the support, by Stacks 04KB
in the form `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`, and a module
with empty support is zero. -/
theorem isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS X.1 X.2) (W : Set (points B S hS X.1)) (hW : IsOpen W)
    (hdisj : W ∩ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) = ∅) :
    IsZero ((restrictToOpenPoints.{u, m} B S hS X W hW).obj M) := by
  refine isZero_of_supportOfSheaf_eq_empty B S hS (openPointsSubspace B S hS X W hW) _ ?_
  rw [restrictToOpenPoints, supportOfSheaf_toSheaf_etaleModulePullback]
  apply Set.eq_empty_of_forall_notMem
  intro z hz
  refine Set.eq_empty_iff_forall_notMem.mp hdisj
    (pointsMap B S hS (openPointsSubspace B S hS X W hW).1
      (openPointsSubspaceHom B S hS X W hW).hom z) ⟨?_, hz⟩
  exact (range_pointsMap_openPointsSubspaceHom B S hS X W hW).subset ⟨z, rfl⟩

/-! ### Vanishing near a geometric point with vanishing stalk -/

/-- A point of an algebraic space at which *some* geometric point has a vanishing stalk is
outside the support of the sheaf: by Stacks 04K4 the set-valued stalk functors at two geometric
points over the same point are isomorphic. -/
theorem notMem_supportOfSheaf_of_subsingleton_stalkSet (X : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{w})
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hstalk : Subsingleton (stalkSet p (F.obj ⋙ forget AddCommGrpCat.{w}))) :
    x ∉ supportOfSheaf B S hS X.1 F := by
  rintro ⟨q, hq, hn⟩
  obtain ⟨e⟩ := stalkSetFunctor_iso_of_liesOver.{u, w} X.2 q p hq hp
  exact hn ((e.app (F.obj ⋙ forget AddCommGrpCat.{w})).toEquiv.subsingleton_congr.mpr hstalk)

/-- **The spreading-out lemma.**  A module of finite type on the small étale site of an
algebraic space whose stalk at a geometric point vanishes vanishes on an open neighbourhood of
the image of that point.

The support of a module of finite type is closed, by Stacks 07TZ, and the given point is
outside it, so its complement is such an open neighbourhood. -/
theorem exists_isOpen_isZero_restrictToOpenPoints (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, m} B S hS X.1 X.2) [SheafOfModules.IsFiniteTypeOnSite M]
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hstalk : Subsingleton (stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m}))) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      IsZero ((restrictToOpenPoints.{u, m} B S hS X W hW).obj M) := by
  set T := supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) with hT
  have hclosed : IsClosed T := isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 M
  have hx : x ∉ T :=
    notMem_supportOfSheaf_of_subsingleton_stalkSet B S hS X _ x p hp hstalk
  refine ⟨Tᶜ, hclosed.isOpen_compl, hx, ?_⟩
  refine isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf B S hS X M _ _ ?_
  rw [← hT]
  exact Set.compl_inter_self T

/-! ### Set-valued stalks of modules at a geometric point -/

/-- The set-valued stalk at a geometric point of the abelian sheaf underlying an `𝒪_X`-module,
as a functor on the category of `𝒪_X`-modules. -/
noncomputable def moduleStalkSetFunctor (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) :
    Modules.{u, m} B S hS X.1 X.2 ⥤ Type (max (u + 1) m) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
    (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{m}) ⋙ stalkSetFunctor p

/-- The stalk functor of `𝒪_X`-modules evaluates to the set-valued stalk of the underlying
abelian sheaf. -/
theorem moduleStalkSetFunctor_obj (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) (M : Modules.{u, m} B S hS X.1 X.2) :
    (moduleStalkSetFunctor B S hS X p).obj M =
      stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m}) :=
  rfl

/-- **The map `φ_x̄` of Stacks 07UF.**  The map on set-valued stalks at a geometric point
induced by a morphism of `𝒪_X`-modules. -/
noncomputable def moduleStalkSetMap (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N) :
    stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m}) →
      stalkSet p (N.val.presheaf ⋙ forget AddCommGrpCat.{m}) :=
  stalkSetMap p (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map φ.val)
    (forget AddCommGrpCat.{m}))

/-- The stalk functor of `𝒪_X`-modules acts on a morphism by the induced map on stalks. -/
theorem moduleStalkSetFunctor_map (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N) :
    (moduleStalkSetFunctor B S hS X p).map φ =
      TypeCat.ofHom (moduleStalkSetMap B S hS X p φ) :=
  rfl

/-- **The set-valued stalk functor on `𝒪_X`-modules is left exact.**  Passing to the underlying
presheaf of abelian groups and then to sets preserves finite limits, and the set-valued stalk of
a presheaf at a geometric point preserves finite limits by Stacks 04K1, part (4). -/
theorem preservesFiniteLimits_moduleStalkSetFunctor (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) :
    PreservesFiniteLimits (moduleStalkSetFunctor.{u, m} B S hS X p) := by
  let H : ((SmallEtale B S hS X.1)ᵒᵖ ⥤ Type m) ⥤ Type (max (u + 1) m) := stalkSetFunctor p
  have hH : PreservesFiniteLimits H :=
    presheafSetStalk_preservesFiniteLimits B S hS X.1 X.2 p
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let A := SheafOfModules.forget.{m} R ⋙ PresheafOfModules.toPresheaf R.obj
  let G := (Functor.whiskeringRight (SmallEtale B S hS X.1)ᵒᵖ AddCommGrpCat.{m}
    (Type m)).obj (forget AddCommGrpCat.{m})
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ A (G ⋙ H) inferInstance
    (comp_preservesFiniteLimits G H)

/-- The set-valued stalk of the zero `𝒪_X`-module at a geometric point is a subsingleton: the
stalk functor is left exact, so it carries the zero module to a terminal set. -/
theorem subsingleton_moduleStalkSetFunctor_obj_zero (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) :
    Subsingleton ((moduleStalkSetFunctor.{u, m} B S hS X p).obj 0) := by
  have := preservesFiniteLimits_moduleStalkSetFunctor.{u, m} B S hS X p
  have : Unique ((moduleStalkSetFunctor.{u, m} B S hS X p).obj 0) :=
    Types.isTerminalEquivUnique _
      ((isZero_zero _).isTerminal.isTerminalObj (moduleStalkSetFunctor.{u, m} B S hS X p) _)
  infer_instance

/-- The zero morphism of `𝒪_X`-modules induces a constant map on set-valued stalks, because it
factors through the zero module and the stalk of the zero module is a subsingleton. -/
theorem moduleStalkSetMap_zero_eq (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, m} B S hS X.1 X.2}
    (a b : stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m})) :
    moduleStalkSetMap B S hS X p (0 : M ⟶ N) a =
      moduleStalkSetMap B S hS X p (0 : M ⟶ N) b := by
  have := subsingleton_moduleStalkSetFunctor_obj_zero.{u, m} B S hS X p
  set T := moduleStalkSetFunctor.{u, m} B S hS X p
  change T.map (0 : M ⟶ N) a = T.map (0 : M ⟶ N) b
  rw [show (0 : M ⟶ N) = (0 : M ⟶ 0) ≫ (0 : (0 : Modules.{u, m} B S hS X.1 X.2) ⟶ N) by simp,
    Functor.map_comp]
  exact congrArg (T.map (0 : (0 : Modules.{u, m} B S hS X.1 X.2) ⟶ N))
    (Subsingleton.elim _ _)

/-- Two successive maps of `𝒪_X`-modules with zero composite induce a map on set-valued stalks
whose composite is constant. -/
private theorem moduleStalkSetMap_comp_eq_of_comp_eq_zero (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {L M N : Modules.{u, m} B S hS X.1 X.2} {f : L ⟶ M}
    {g : M ⟶ N} (h : f ≫ g = 0)
    (a b : stalkSet p (L.val.presheaf ⋙ forget AddCommGrpCat.{m})) :
    moduleStalkSetMap B S hS X p g (moduleStalkSetMap B S hS X p f a) =
      moduleStalkSetMap B S hS X p g (moduleStalkSetMap B S hS X p f b) := by
  set T := moduleStalkSetFunctor.{u, m} B S hS X p
  change (T.map f ≫ T.map g) a = (T.map f ≫ T.map g) b
  rw [← Functor.map_comp, h]
  exact moduleStalkSetMap_zero_eq B S hS X p a b

/-- A monomorphism of `𝒪_X`-modules is injective on the set-valued stalk at every geometric
point, the stalk functor being left exact. -/
theorem injective_moduleStalkSetMap_of_mono (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    [Mono φ] : Function.Injective (moduleStalkSetMap B S hS X p φ) := by
  have := preservesFiniteLimits_moduleStalkSetFunctor.{u, m} B S hS X p
  exact (mono_iff_injective ((moduleStalkSetFunctor.{u, m} B S hS X p).map φ)).1 inferInstance

/-- **An epimorphism of `𝒪_X`-modules is surjective on the set-valued stalk at every geometric
point.**  An epimorphism of sheaves of modules is locally surjective on underlying abelian
sheaves, and local surjectivity is detected on geometric stalks by Stacks 04K5. -/
theorem surjective_moduleStalkSetMap_of_epi (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    [Epi φ] : Function.Surjective (moduleStalkSetMap B S hS X p φ) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let A := SheafOfModules.toSheaf.{u} R
  let T := A ⋙ sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})
  have : PreservesFiniteColimits A := PreservesColimitsOfSize.preservesFiniteColimits A
  exact (surjective_iff_stalkSetMap_surjective B S hS X.1 X.2 (T.map φ)).1
    ((Presheaf.isLocallySurjective_iff_whisker_forget (SmallEtale.topology B S hS X.1)
      (A.map φ).hom).1 ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat (A.map φ)).2
        inferInstance)) p

/-- If a morphism of `𝒪_X`-modules is injective on the set-valued stalk at a geometric point,
the stalk of its kernel at that point is a subsingleton. -/
theorem subsingleton_moduleStalkSet_kernel_of_injective (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, m} B S hS X.1 X.2} (φ : M ⟶ N)
    (hinj : Function.Injective (moduleStalkSetMap B S hS X p φ)) :
    Subsingleton (stalkSet p ((kernel φ).val.presheaf ⋙ forget AddCommGrpCat.{m})) := by
  refine ⟨fun a b => injective_moduleStalkSetMap_of_mono B S hS X p (kernel.ι φ)
    (hinj (moduleStalkSetMap_comp_eq_of_comp_eq_zero B S hS X p (kernel.condition φ) a b))⟩

/-- If a morphism of `𝒪_X`-modules is surjective on the set-valued stalk at a geometric point,
the stalk of its cokernel at that point is a subsingleton. -/
theorem subsingleton_moduleStalkSet_cokernel_of_surjective (X : AlgebraicSpaces B S hS)
    (p : GeometricPoint B S hS X.1) {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (hsurj : Function.Surjective (moduleStalkSetMap B S hS X p φ)) :
    Subsingleton (stalkSet p ((cokernel φ).val.presheaf ⋙ forget AddCommGrpCat.{u})) := by
  have hπ := surjective_moduleStalkSetMap_of_epi B S hS X p (cokernel.π φ)
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ.comp hsurj a
  obtain ⟨b, rfl⟩ := hπ.comp hsurj b
  exact moduleStalkSetMap_comp_eq_of_comp_eq_zero B S hS X p (cokernel.condition φ) a b

/-! ### Finite type from coherence -/

/-- An `𝒪_X`-module coherent on the small étale site is of finite type on that site, by
Stacks 03DL(8) and the passage from the sectionwise to the categorical form of Stacks
03DL(5). -/
theorem isFiniteTypeOnSite_of_isCoherentOnSite (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) [SheafOfModules.IsCoherentOnSite M] :
    SheafOfModules.IsFiniteTypeOnSite M :=
  Stacks.SheafOfModules.isFiniteTypeOnSite_of_presheaf_isFiniteType M
    SheafOfModules.IsCoherentOnSite.isFiniteType

/-- The kernel of a morphism of `𝒪_X`-modules coherent on the small étale site is of finite
type on that site: it is coherent by Stacks 01BY(3), and a coherent module is of finite type. -/
theorem isFiniteTypeOnSite_kernel (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} [SheafOfModules.IsCoherentOnSite M]
    [SheafOfModules.IsCoherentOnSite N] (φ : M ⟶ N) :
    SheafOfModules.IsFiniteTypeOnSite (kernel φ) :=
  have := Stacks.SheafOfModules.isCoherentOnSite_kernel
    ‹SheafOfModules.IsCoherentOnSite M› ‹SheafOfModules.IsCoherentOnSite N› φ
  isFiniteTypeOnSite_of_isCoherentOnSite B S hS X (kernel φ)

/-- The cokernel of a morphism of `𝒪_X`-modules coherent on the small étale site is of finite
type on that site: it is coherent by Stacks 01BY(3), and a coherent module is of finite type. -/
theorem isFiniteTypeOnSite_cokernel (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} [SheafOfModules.IsCoherentOnSite M]
    [SheafOfModules.IsCoherentOnSite N] (φ : M ⟶ N) :
    SheafOfModules.IsFiniteTypeOnSite (cokernel φ) :=
  have := Stacks.SheafOfModules.isCoherentOnSite_cokernel φ
    ‹SheafOfModules.IsCoherentOnSite M› ‹SheafOfModules.IsCoherentOnSite N›
  isFiniteTypeOnSite_of_isCoherentOnSite B S hS X (cokernel φ)

/-! ### Transport of exactness to an open subspace -/

/-- A morphism of `𝒪_X`-modules whose kernel vanishes on an open subspace restricts to a
monomorphism there: étale restriction of modules is left exact, so it carries the kernel of the
morphism to the kernel of its restriction. -/
theorem mono_restrictToOpenPoints_map_of_isZero_kernel (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : IsZero ((restrictToOpenPoints.{u, u} B S hS X W hW).obj (kernel φ))) :
    Mono ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ) := by
  have : PreservesFiniteLimits (restrictToOpenPoints.{u, u} B S hS X W hW) :=
    preservesFiniteLimits_etaleModulePullback B S hS (openPointsSubspaceHom B S hS X W hW)
      (isEtale_openPointsSubspaceHom B S hS X W hW)
  have hz : IsZero (kernel ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ)) :=
    (Iso.isZero_iff (PreservesKernel.iso (restrictToOpenPoints.{u, u} B S hS X W hW) φ)).1 h
  exact Preadditive.mono_of_kernel_zero (hz.eq_of_src _ _)

/-- A morphism of `𝒪_X`-modules whose cokernel vanishes on an open subspace restricts to an
epimorphism there: étale restriction of modules is right exact, so it carries the cokernel of
the morphism to the cokernel of its restriction. -/
theorem epi_restrictToOpenPoints_map_of_isZero_cokernel (X : AlgebraicSpaces B S hS)
    (W : Set (points B S hS X.1)) (hW : IsOpen W)
    {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (h : IsZero ((restrictToOpenPoints.{u, u} B S hS X W hW).obj (cokernel φ))) :
    Epi ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ) := by
  have : PreservesFiniteColimits (restrictToOpenPoints.{u, u} B S hS X W hW) :=
    preservesFiniteColimits_etaleModulePullback B S hS (openPointsSubspaceHom B S hS X W hW)
      (isEtale_openPointsSubspaceHom B S hS X W hW)
  have hz : IsZero (cokernel ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ)) :=
    (Iso.isZero_iff (PreservesCokernel.iso (restrictToOpenPoints.{u, u} B S hS X W hW) φ)).1 h
  exact Preadditive.epi_of_cokernel_zero (hz.eq_of_tgt _ _)

/-- Two `𝒪_X`-modules of finite type whose stalks at a geometric point both vanish vanish on a
single open subspace containing the image of that point: the complement of the union of their
supports, which is closed by Stacks 07TZ. -/
theorem exists_isOpen_isZero_restrictToOpenPoints_pair (X : AlgebraicSpaces B S hS)
    (M N : Modules.{u, m} B S hS X.1 X.2) [SheafOfModules.IsFiniteTypeOnSite M]
    [SheafOfModules.IsFiniteTypeOnSite N]
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hM : Subsingleton (stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{m})))
    (hN : Subsingleton (stalkSet p (N.val.presheaf ⋙ forget AddCommGrpCat.{m}))) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      IsZero ((restrictToOpenPoints.{u, m} B S hS X W hW).obj M) ∧
      IsZero ((restrictToOpenPoints.{u, m} B S hS X W hW).obj N) := by
  have hcM : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 M
  have hcN : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N)) :=
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.2 N
  refine ⟨(supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) ∪
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N))ᶜ,
    (hcM.union hcN).isOpen_compl, ?_, ?_, ?_⟩
  · rintro (h | h)
    · exact notMem_supportOfSheaf_of_subsingleton_stalkSet B S hS X _ x p hp hM h
    · exact notMem_supportOfSheaf_of_subsingleton_stalkSet B S hS X _ x p hp hN h
  · exact isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf B S hS X M _ _
      (Set.eq_empty_of_forall_notMem fun _ hz => hz.1 (Or.inl hz.2))
  · exact isZero_restrictToOpenPoints_of_disjoint_supportOfSheaf B S hS X N _ _
      (Set.eq_empty_of_forall_notMem fun _ hz => hz.1 (Or.inr hz.2))

/-! ### Stacks 07UF -/

/-- **Stacks 07UF, part (1).**  A coherent `𝒪_X`-module whose stalk at a geometric point `x̄`
vanishes vanishes on an open subspace of `X` containing the image of `x̄`.

The locally Noetherian hypothesis of the cited statement is not used: the support of a module of
finite type is closed by Stacks 07TZ on any algebraic space, so the statement here is a strict
generalisation. -/
@[stacks 07UF "part (1)"]
theorem exists_isOpen_isZero_restrictToOpenPoints_of_isCoherent (X : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS X.1 X.2) [IsCoherent B S hS X.1 X.2 M]
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hstalk : Subsingleton (stalkSet p (M.val.presheaf ⋙ forget AddCommGrpCat.{u}))) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      IsZero ((restrictToOpenPoints.{u, u} B S hS X W hW).obj M) :=
  have := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X M
  exists_isOpen_isZero_restrictToOpenPoints B S hS X M x p hp hstalk

/-- **Stacks 07UF, part (2).**  A morphism of coherent `𝒪_X`-modules injective on the stalk at a
geometric point `x̄` is a monomorphism after restriction to an open subspace of `X` containing
the image of `x̄`.

The kernel is coherent on the small étale site, hence of finite type, and its stalk at `x̄`
vanishes; part (1) applies to it, and étale restriction is left exact.  The locally Noetherian
hypothesis of the cited statement is not used. -/
@[stacks 07UF "part (2)"]
theorem exists_isOpen_mono_restrictToOpenPoints_map (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} [IsCoherent B S hS X.1 X.2 M]
    [IsCoherent B S hS X.1 X.2 N] (φ : M ⟶ N)
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hinj : Function.Injective (moduleStalkSetMap B S hS X p φ)) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      Mono ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ) := by
  have := isFiniteTypeOnSite_kernel B S hS X φ
  obtain ⟨W, hW, hxW, hzero⟩ :=
    exists_isOpen_isZero_restrictToOpenPoints B S hS X (kernel φ) x p hp
      (subsingleton_moduleStalkSet_kernel_of_injective B S hS X p φ hinj)
  exact ⟨W, hW, hxW, mono_restrictToOpenPoints_map_of_isZero_kernel B S hS X W hW φ hzero⟩

/-- **Stacks 07UF, part (3).**  A morphism of coherent `𝒪_X`-modules surjective on the stalk at
a geometric point `x̄` is an epimorphism after restriction to an open subspace of `X` containing
the image of `x̄`.

The cokernel is coherent on the small étale site, hence of finite type, and its stalk at `x̄`
vanishes; part (1) applies to it, and étale restriction is right exact.  The locally Noetherian
hypothesis of the cited statement is not used. -/
@[stacks 07UF "part (3)"]
theorem exists_isOpen_epi_restrictToOpenPoints_map (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} [IsCoherent B S hS X.1 X.2 M]
    [IsCoherent B S hS X.1 X.2 N] (φ : M ⟶ N)
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hsurj : Function.Surjective (moduleStalkSetMap B S hS X p φ)) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      Epi ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ) := by
  have := isFiniteTypeOnSite_cokernel B S hS X φ
  obtain ⟨W, hW, hxW, hzero⟩ :=
    exists_isOpen_isZero_restrictToOpenPoints B S hS X (cokernel φ) x p hp
      (subsingleton_moduleStalkSet_cokernel_of_surjective B S hS X p φ hsurj)
  exact ⟨W, hW, hxW, epi_restrictToOpenPoints_map_of_isZero_cokernel B S hS X W hW φ hzero⟩

/-- **Stacks 07UF, part (4).**  A morphism of coherent `𝒪_X`-modules bijective on the stalk at a
geometric point `x̄` becomes an isomorphism after restriction to an open subspace of `X`
containing the image of `x̄`.

Kernel and cokernel are both of finite type with vanishing stalk at `x̄`, so both vanish on the
complement of the union of their two closed supports; there the restriction is both a
monomorphism and an epimorphism.  The locally Noetherian hypothesis of the cited statement is
not used. -/
@[stacks 07UF "part (4)"]
theorem exists_isOpen_isIso_restrictToOpenPoints_map (X : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS X.1 X.2} [IsCoherent B S hS X.1 X.2 M]
    [IsCoherent B S hS X.1 X.2 N] (φ : M ⟶ N)
    (x : points B S hS X.1) (p : GeometricPoint B S hS X.1) (hp : p.LiesOver x)
    (hbij : Function.Bijective (moduleStalkSetMap B S hS X p φ)) :
    ∃ (W : Set (points B S hS X.1)) (hW : IsOpen W), x ∈ W ∧
      IsIso ((restrictToOpenPoints.{u, u} B S hS X W hW).map φ) := by
  have := isFiniteTypeOnSite_kernel B S hS X φ
  have := isFiniteTypeOnSite_cokernel B S hS X φ
  obtain ⟨W, hW, hxW, hk, hc⟩ :=
    exists_isOpen_isZero_restrictToOpenPoints_pair B S hS X (kernel φ) (cokernel φ) x p hp
      (subsingleton_moduleStalkSet_kernel_of_injective B S hS X p φ hbij.1)
      (subsingleton_moduleStalkSet_cokernel_of_surjective B S hS X p φ hbij.2)
  have := mono_restrictToOpenPoints_map_of_isZero_kernel B S hS X W hW φ hk
  have := epi_restrictToOpenPoints_map_of_isZero_cokernel B S hS X W hW φ hc
  exact ⟨W, hW, hxW, isIso_of_mono_of_epi _⟩

end AlgebraicGeometry.Space

end
