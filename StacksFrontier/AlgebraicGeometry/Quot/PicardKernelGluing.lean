module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardInvertibleDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PicardKernelSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentTransitivity

/-!
# Gluing invertible modules trivialised along the section

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` with a section `σ`, and
assume `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T`, the hypothesis of
Stacks 0D28.  This file proves the gluing half of the sheaf property in the proof of
Stacks 0D28: invertible modules `L_i` on the base changes `X_{U_i}` of an fpqc covering family
`{U_i ⟶ T}`, each trivialised along the section, which become isomorphic on the base changes of
all test schemes over two of the `U_i`, glue to an invertible module on `X_T`.

On the base change of each overlap `U_i ×_T U_j` an isomorphism
`φ_{ij}` of the two restrictions is chosen *normalised* along the section
(`AlgebraicGeometry.Space.PicardSituation.exists_isNormalized`), which is the rescaling by
`u_{ij}^{-1}` in the source.  The cocycle condition holds because on a triple overlap both sides
are normalised isomorphisms between the same two modules, and these are unique
(`AlgebraicGeometry.Space.PicardSituation.IsNormalized.eq`) — the source's `f_{ijk} = 1`.  The
descent datum so obtained is effective by the fpqc descent of quasi-coherent modules on algebraic
spaces, Stacks 04W8, and the module it descends to is invertible because invertibility descends
along fpqc coverings
(`AlgebraicGeometry.Space.isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite`).

## Main results

* `AlgebraicGeometry.Space.PicardSituation.overlapTestHom`: a morphism of test schemes into the
  overlap of two test schemes, from a pair of morphisms agreeing over the target.
* `AlgebraicGeometry.Space.PicardSituation.exists_isInvertibleModule_glue`: **the gluing step of
  Stacks 0D28.**

## References

* [Stacks Project, Tag 0D28](https://stacks.math.columbia.edu/tag/0D28)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A pairwise isomorphism of a descent datum read on a test space is its restriction. -/
theorem QuasiCoherentDescent.transitionOn_eq_restrictPullbackIso {I : Type v}
    {X : AlgebraicSpaces B S hS} (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (QuasiCoherentDescent.pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (QuasiCoherentDescent.pairSnd B S hS Y f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ QuasiCoherentDescent.pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ QuasiCoherentDescent.pairFst B S hS Y f i j = vi)
    (hj : v ≫ QuasiCoherentDescent.pairSnd B S hS Y f i j = vj) :
    QuasiCoherentDescent.transitionOn B S hS Y f F φ i j v vi vj hi hj =
      restrictPullbackIso v hi hj (φ i j) := by
  subst hi hj
  rfl

namespace PicardSituation

variable {s : PicardSituation B S hS} (σ : s.base ⟶ s.X) (hσ : σ ≫ s.f = 𝟙 s.base)

attribute [local instance] BigFppfSite.hasPullbacks_schemes

/-- **A morphism of test schemes into an overlap**: two morphisms `a : W ⟶ U`, `b : W ⟶ U'`
agreeing over `T` define a morphism into the overlap `U ×_T U'`. -/
def overlapTestHom {T U U' W : s.SchemesOver} (g : U ⟶ T) (g' : U' ⟶ T) (a : W ⟶ U)
    (b : W ⟶ U') (h : a ≫ g = b ≫ g') : W ⟶ s.overlapSituation.overlapTest g g' :=
  CostructuredArrow.homMk (pullback.lift a.left b.left (congrArg CommaMorphism.left h)) (by
    rw [CostructuredArrow.mk_hom_eq_self, ← Category.assoc, ← Functor.map_comp,
      pullback.lift_fst]
    exact CostructuredArrow.w a)

/-- The morphism into the overlap followed by the first projection is the first morphism. -/
@[reassoc (attr := simp)]
theorem overlapTestHom_fst {T U U' W : s.SchemesOver} (g : U ⟶ T) (g' : U' ⟶ T) (a : W ⟶ U)
    (b : W ⟶ U') (h : a ≫ g = b ≫ g') :
    overlapTestHom g g' a b h ≫ s.overlapSituation.overlapTestFst g g' = a :=
  CostructuredArrow.hom_ext _ _ (pullback.lift_fst _ _ _)

/-- The morphism into the overlap followed by the second projection is the second morphism. -/
@[reassoc (attr := simp)]
theorem overlapTestHom_snd {T U U' W : s.SchemesOver} (g : U ⟶ T) (g' : U' ⟶ T) (a : W ⟶ U)
    (b : W ⟶ U') (h : a ≫ g = b ≫ g') :
    overlapTestHom g g' a b h ≫ s.overlapSituation.overlapTestSnd g g' = b :=
  CostructuredArrow.hom_ext _ _ (pullback.lift_snd _ _ _)

section Triple

variable {T : s.SchemesOver} {I : Type v} {U : I → s.SchemesOver} (g : ∀ i, U i ⟶ T)

/-- The triple overlap `U_i ×_T U_j ×_T U_k` of three members of a family of test schemes. -/
abbrev tripleTest (i j k : I) : s.SchemesOver :=
  s.overlapSituation.overlapTest (s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i) (g k)

/-- The projection of the triple overlap to the overlap of the first two members. -/
abbrev tripleToPair₁₂ (i j k : I) :
    tripleTest g i j k ⟶ s.overlapSituation.overlapTest (g i) (g j) :=
  s.overlapSituation.overlapTestFst _ _

/-- The projection of the triple overlap to the first member. -/
abbrev tripleProj₁ (i j k : I) : tripleTest g i j k ⟶ U i :=
  tripleToPair₁₂ g i j k ≫ s.overlapSituation.overlapTestFst (g i) (g j)

/-- The projection of the triple overlap to the second member. -/
abbrev tripleProj₂ (i j k : I) : tripleTest g i j k ⟶ U j :=
  tripleToPair₁₂ g i j k ≫ s.overlapSituation.overlapTestSnd (g i) (g j)

/-- The projection of the triple overlap to the third member. -/
abbrev tripleProj₃ (i j k : I) : tripleTest g i j k ⟶ U k :=
  s.overlapSituation.overlapTestSnd _ _

/-- The projections of the triple overlap to the first and the third member agree over `T`. -/
theorem tripleProj₁_comp (i j k : I) : tripleProj₁ g i j k ≫ g i = tripleProj₃ g i j k ≫ g k := by
  rw [Category.assoc]
  exact s.overlapSituation.overlapTest_condition _ _

/-- The projections of the triple overlap to the second and the third member agree over `T`. -/
theorem tripleProj₂_comp (i j k : I) : tripleProj₂ g i j k ≫ g j = tripleProj₃ g i j k ≫ g k := by
  rw [← tripleProj₁_comp, Category.assoc, Category.assoc,
    s.overlapSituation.overlapTest_condition (g i) (g j)]

/-- The projection of the triple overlap to the overlap of the last two members. -/
abbrev tripleToPair₂₃ (i j k : I) :
    tripleTest g i j k ⟶ s.overlapSituation.overlapTest (g j) (g k) :=
  overlapTestHom (g j) (g k) (tripleProj₂ g i j k) (tripleProj₃ g i j k) (tripleProj₂_comp g i j k)

/-- The projection of the triple overlap to the overlap of the first and the last member. -/
abbrev tripleToPair₁₃ (i j k : I) :
    tripleTest g i j k ⟶ s.overlapSituation.overlapTest (g i) (g k) :=
  overlapTestHom (g i) (g k) (tripleProj₁ g i j k) (tripleProj₃ g i j k) (tripleProj₁_comp g i j k)

/-- **A test space mapping compatibly to three members of the base-changed family factors through
the base change of their triple overlap**, compatibly with the comparison maps of the three
pairwise fibre products. -/
theorem exists_tripleLift (i j k : I) {Z : AlgebraicSpaces B S hS}
    (vi : Z ⟶ s.baseChange (U i)) (vj : Z ⟶ s.baseChange (U j)) (vk : Z ⟶ s.baseChange (U k))
    (vij : Z ⟶ AlgebraicSpaces.fiberProduct B S hS (baseChangeMap s.f (g i))
      (baseChangeMap s.f (g j)))
    (vjk : Z ⟶ AlgebraicSpaces.fiberProduct B S hS (baseChangeMap s.f (g j))
      (baseChangeMap s.f (g k)))
    (vik : Z ⟶ AlgebraicSpaces.fiberProduct B S hS (baseChangeMap s.f (g i))
      (baseChangeMap s.f (g k)))
    (hij₀ : vij ≫ fiberFst (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j)) = vi)
    (hij₁ : vij ≫ fiberSnd (baseChangeMap s.f (g i)) (baseChangeMap s.f (g j)) = vj)
    (hjk₀ : vjk ≫ fiberFst (baseChangeMap s.f (g j)) (baseChangeMap s.f (g k)) = vj)
    (hjk₁ : vjk ≫ fiberSnd (baseChangeMap s.f (g j)) (baseChangeMap s.f (g k)) = vk)
    (hik₀ : vik ≫ fiberFst (baseChangeMap s.f (g i)) (baseChangeMap s.f (g k)) = vi)
    (hik₁ : vik ≫ fiberSnd (baseChangeMap s.f (g i)) (baseChangeMap s.f (g k)) = vk) :
    ∃ w : Z ⟶ s.baseChange (tripleTest g i j k),
      vij ≫ s.overlapSituation.overlapTestComparison (g i) (g j) =
        w ≫ baseChangeMap s.f (tripleToPair₁₂ g i j k) ∧
      vjk ≫ s.overlapSituation.overlapTestComparison (g j) (g k) =
        w ≫ baseChangeMap s.f (tripleToPair₂₃ g i j k) ∧
      vik ≫ s.overlapSituation.overlapTestComparison (g i) (g k) =
        w ≫ baseChangeMap s.f (tripleToPair₁₃ g i j k) := by
  have eij : vi ≫ baseChangeMap s.f (g i) = vj ≫ baseChangeMap s.f (g j) := by
    rw [← hij₀, ← hij₁, Category.assoc, Category.assoc,
      (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _).w]
  have eik : vi ≫ baseChangeMap s.f (g i) = vk ≫ baseChangeMap s.f (g k) := by
    rw [← hik₀, ← hik₁, Category.assoc, Category.assoc,
      (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _).w]
  have incl : ∀ (a : I) (v : Z ⟶ s.baseChange (U a)), (v ≫ baseChangeInclusion s.f (U a)) ≫
      spaceMap (g a) = (v ≫ baseChangeMap s.f (g a)) ≫ baseChangeInclusion s.f T := by
    intro a v
    rw [Category.assoc, Category.assoc, baseChangeMap_comp_inclusion]
  have P := HomSituation.isPullback_schemeSpaceFunctor (g i).left (g j).left
  have P' := HomSituation.isPullback_schemeSpaceFunctor
    (s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i).left (g k).left
  let zij := P.lift (vi ≫ baseChangeInclusion s.f (U i)) (vj ≫ baseChangeInclusion s.f (U j))
    (by rw [incl i vi, incl j vj, eij])
  have zij₁ : zij ≫ spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) =
      vi ≫ baseChangeInclusion s.f (U i) := P.lift_fst _ _ _
  have zij₂ : zij ≫ spaceMap (s.overlapSituation.overlapTestSnd (g i) (g j)) =
      vj ≫ baseChangeInclusion s.f (U j) := P.lift_snd _ _ _
  let z₃ := P'.lift zij (vk ≫ baseChangeInclusion s.f (U k)) (by
    change zij ≫ spaceMap (s.overlapSituation.overlapTestFst (g i) (g j) ≫ g i) = _
    rw [spaceMap_comp, ← Category.assoc, zij₁, incl i vi, incl k vk, eik])
  have z₃₁ : z₃ ≫ spaceMap (tripleToPair₁₂ g i j k) = zij := P'.lift_fst _ _ _
  have z₃₂ : z₃ ≫ spaceMap (tripleProj₃ g i j k) = vk ≫ baseChangeInclusion s.f (U k) :=
    P'.lift_snd _ _ _
  let w : Z ⟶ s.baseChange (tripleTest g i j k) :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS s.f (tripleTest g i j k).hom).lift
    (vi ≫ baseChangeProjection s.f (U i)) z₃ (by
      change _ = z₃ ≫ (spaceMap (tripleToPair₁₂ g i j k) ≫
        (spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ (U i).hom))
      rw [← Category.assoc, z₃₁, ← Category.assoc, zij₁, Category.assoc, Category.assoc,
        baseChangeProjection_comp])
  have w₁ : w ≫ baseChangeProjection s.f (tripleTest g i j k) =
      vi ≫ baseChangeProjection s.f (U i) :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _).lift_fst _ _ _
  have w₂ : w ≫ baseChangeInclusion s.f (tripleTest g i j k) = z₃ :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _).lift_snd _ _ _
  have pj : vj ≫ baseChangeProjection s.f (U j) = vi ≫ baseChangeProjection s.f (U i) := by
    rw [← baseChangeMap_comp_projection s.f (g i), ← baseChangeMap_comp_projection s.f (g j),
      ← Category.assoc, ← Category.assoc, eij]
  have pk : vk ≫ baseChangeProjection s.f (U k) = vi ≫ baseChangeProjection s.f (U i) := by
    rw [← baseChangeMap_comp_projection s.f (g i), ← baseChangeMap_comp_projection s.f (g k),
      ← Category.assoc, ← Category.assoc, eik]
  have hproj : ∀ {a b : I} (v : Z ⟶ AlgebraicSpaces.fiberProduct B S hS (baseChangeMap s.f (g a))
      (baseChangeMap s.f (g b))) (va : Z ⟶ s.baseChange (U a))
      (hva : v ≫ fiberFst (baseChangeMap s.f (g a)) (baseChangeMap s.f (g b)) = va)
      (hpa : va ≫ baseChangeProjection s.f (U a) = vi ≫ baseChangeProjection s.f (U i))
      (h : tripleTest g i j k ⟶ s.overlapSituation.overlapTest (g a) (g b)),
      (v ≫ s.overlapSituation.overlapTestComparison (g a) (g b)) ≫
        baseChangeProjection s.f (s.overlapSituation.overlapTest (g a) (g b)) =
      (w ≫ baseChangeMap s.f h) ≫
        baseChangeProjection s.f (s.overlapSituation.overlapTest (g a) (g b)) := by
    intro a b v va hva hpa h
    rw [Category.assoc, s.overlapSituation.overlapTestComparison_comp_projection,
      ← Category.assoc, hva, hpa, Category.assoc, baseChangeMap_comp_projection, w₁]
  have hlf : ∀ a b : I, s.overlapSituation.overlapTestLift (g a) (g b) ≫
      spaceMap (s.overlapSituation.overlapTestFst (g a) (g b)) =
      fiberFst (baseChangeMap s.f (g a)) (baseChangeMap s.f (g b)) ≫
        baseChangeInclusion s.f (U a) :=
    fun a b ↦ s.overlapSituation.overlapTestLift_comp_fst (g a) (g b)
  have hls : ∀ a b : I, s.overlapSituation.overlapTestLift (g a) (g b) ≫
      spaceMap (s.overlapSituation.overlapTestSnd (g a) (g b)) =
      fiberSnd (baseChangeMap s.f (g a)) (baseChangeMap s.f (g b)) ≫
        baseChangeInclusion s.f (U b) :=
    fun a b ↦ s.overlapSituation.overlapTestLift_comp_snd (g a) (g b)
  have hincl : ∀ {a b : I} (v : Z ⟶ AlgebraicSpaces.fiberProduct B S hS (baseChangeMap s.f (g a))
      (baseChangeMap s.f (g b))) (va : Z ⟶ s.baseChange (U a)) (vb : Z ⟶ s.baseChange (U b))
      (hva : v ≫ fiberFst (baseChangeMap s.f (g a)) (baseChangeMap s.f (g b)) = va)
      (hvb : v ≫ fiberSnd (baseChangeMap s.f (g a)) (baseChangeMap s.f (g b)) = vb)
      (h : tripleTest g i j k ⟶ s.overlapSituation.overlapTest (g a) (g b))
      (ha : z₃ ≫ spaceMap (h ≫ s.overlapSituation.overlapTestFst (g a) (g b)) =
        va ≫ baseChangeInclusion s.f (U a))
      (hb : z₃ ≫ spaceMap (h ≫ s.overlapSituation.overlapTestSnd (g a) (g b)) =
        vb ≫ baseChangeInclusion s.f (U b)),
      (v ≫ s.overlapSituation.overlapTestComparison (g a) (g b)) ≫
        baseChangeInclusion s.f (s.overlapSituation.overlapTest (g a) (g b)) =
      (w ≫ baseChangeMap s.f h) ≫
        baseChangeInclusion s.f (s.overlapSituation.overlapTest (g a) (g b)) := by
    intro a b v va vb hva hvb h ha hb
    rw [Category.assoc, s.overlapSituation.overlapTestComparison_comp_inclusion,
      Category.assoc, baseChangeMap_comp_inclusion, ← Category.assoc, w₂]
    refine (HomSituation.isPullback_schemeSpaceFunctor (g a).left (g b).left).hom_ext ?_ ?_
    · change (v ≫ _) ≫ spaceMap (s.overlapSituation.overlapTestFst (g a) (g b)) =
        (z₃ ≫ spaceMap h) ≫ spaceMap (s.overlapSituation.overlapTestFst (g a) (g b))
      rw [Category.assoc, hlf, ← Category.assoc, hva,
        Category.assoc, ← spaceMap_comp, ha]
    · change (v ≫ _) ≫ spaceMap (s.overlapSituation.overlapTestSnd (g a) (g b)) =
        (z₃ ≫ spaceMap h) ≫ spaceMap (s.overlapSituation.overlapTestSnd (g a) (g b))
      rw [Category.assoc, hls, ← Category.assoc, hvb,
        Category.assoc, ← spaceMap_comp, hb]
  have t₁ : z₃ ≫ spaceMap (tripleProj₁ g i j k) = vi ≫ baseChangeInclusion s.f (U i) := by
    rw [spaceMap_comp, ← Category.assoc, z₃₁, zij₁]
  have t₂ : z₃ ≫ spaceMap (tripleProj₂ g i j k) = vj ≫ baseChangeInclusion s.f (U j) := by
    rw [spaceMap_comp, ← Category.assoc, z₃₁, zij₂]
  refine ⟨w, ?_, ?_, ?_⟩
  · exact baseChange_hom_ext s.f (hproj vij vi hij₀ rfl _) (hincl vij vi vj hij₀ hij₁ _ t₁ t₂)
  · exact baseChange_hom_ext s.f (hproj vjk vj hjk₀ pj _) (hincl vjk vj vk hjk₀ hjk₁ _
      (by rwa [overlapTestHom_fst]) (by rwa [overlapTestHom_snd]))
  · exact baseChange_hom_ext s.f (hproj vik vi hik₀ rfl _) (hincl vik vi vk hik₀ hik₁ _
      (by rwa [overlapTestHom_fst]) (by rwa [overlapTestHom_snd]))

end Triple

/-- **The gluing step of Stacks 0D28.**  Assume `𝒪_V ⟶ f_{V, *}𝒪_{X_V}` is an isomorphism for
every test scheme `V`.  Let `{g_i : U_i ⟶ T}` be a family of test schemes whose underlying
morphisms form an fpqc covering, and let `L_i` be invertible modules on the base changes
`X_{U_i}`, each trivialised along the section, `α_i : σ_{U_i}^*L_i ≅ (g_i ≫ σ_T)^*R`, with
values in the inverse images of one module `R` on `X_T`.  If for every test scheme `V` with
morphisms `a : V ⟶ U_i`, `b : V ⟶ U_j` agreeing over `T` the restrictions of `L_i` and `L_j`
to `X_V` are isomorphic, then there is an invertible module `M` on `X_T` with
`L_i ≅ X_{g_i}^*M` for every `i`. -/
theorem exists_isInvertibleModule_glue (hstr : s.StructureSheafMapIso) {T : s.SchemesOver}
    {I : Type v} {U : I → s.SchemesOver} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ (spaceMap (g i)).hom)
    (R : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (L : ∀ i, Modules.{u, u} B S hS (s.baseChange (U i)).1 (s.baseChange (U i)).2)
    (hL : ∀ i, IsInvertibleModule (s.baseChange (U i)) (L i))
    (α : ∀ i, (modulePullback B S hS (baseChangeSection σ hσ (U i))).obj (L i) ≅
      (modulePullback B S hS (spaceMap (g i) ≫ baseChangeSection σ hσ T)).obj R)
    (hcomp : ∀ (i j : I) {V : s.SchemesOver} (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = b ≫ g j →
      Nonempty ((modulePullback B S hS (baseChangeMap s.f a)).obj (L i) ≅
        (modulePullback B S hS (baseChangeMap s.f b)).obj (L j))) :
    ∃ M : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2,
      IsInvertibleModule (s.baseChange T) M ∧
        ∀ i, Nonempty (L i ≅ (modulePullback B S hS (baseChangeMap s.f (g i))).obj M) := by
  classical
  have hw : ∀ i j : I, spaceMap (s.overlapSituation.overlapTestSnd (g i) (g j)) ≫
      spaceMap (g j) ≫ baseChangeSection σ hσ T =
      spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ spaceMap (g i) ≫
        baseChangeSection σ hσ T := by
    intro i j
    rw [← Category.assoc, ← Category.assoc, ← spaceMap_comp, ← spaceMap_comp,
      s.overlapSituation.overlapTest_condition (g i) (g j)]
  have hex : ∀ i j : I, ∃ ψ, IsNormalized σ hσ R (α i) (α j)
      (s.overlapSituation.overlapTestFst (g i) (g j))
      (s.overlapSituation.overlapTestSnd (g i) (g j))
      (spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ spaceMap (g i) ≫
        baseChangeSection σ hσ T) rfl (hw i j) ψ :=
    fun i j ↦ exists_isNormalized σ hσ (hstr _) (modulePullbackInvertible _ _ (hL i))
      (modulePullbackInvertible _ _ (hL j))
      (hcomp i j _ _ (s.overlapSituation.overlapTest_condition (g i) (g j))).some
  choose ψ hψ using hex
  have hcov : IsFpqcCovering B S hS fun i ↦ (baseChangeMap s.f (g i)).hom :=
    isFpqcCovering_baseChangeMap s.f g hg
  let D : QuasiCoherentDescent.DescentDatum B S hS (fun i ↦ s.baseChange (U i))
      (fun i ↦ baseChangeMap s.f (g i)) :=
    { F := L
      quasicoherent := fun i ↦ isQuasicoherentOnSite_of_isInvertibleModule _ _ (hL i)
      transition := fun i j ↦ restrictPullbackIso
        (s.overlapSituation.overlapTestComparison (g i) (g j))
        (s.overlapSituation.overlapTestComparison_comp_baseChangeMap_fst (g i) (g j))
        (s.overlapSituation.overlapTestComparison_comp_baseChangeMap_snd (g i) (g j)) (ψ i j)
      cocycle := by
        intro i j k Z vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁
        rw [QuasiCoherentDescent.transitionOn_eq_restrictPullbackIso,
          QuasiCoherentDescent.transitionOn_eq_restrictPullbackIso,
          QuasiCoherentDescent.transitionOn_eq_restrictPullbackIso]
        obtain ⟨w, e₁, e₂, e₃⟩ :=
          exists_tripleLift g i j k vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁
        have hW₂ : spaceMap (tripleToPair₂₃ g i j k) ≫
            spaceMap (s.overlapSituation.overlapTestFst (g j) (g k)) ≫ spaceMap (g j) ≫
              baseChangeSection σ hσ T =
            spaceMap (tripleProj₁ g i j k) ≫ spaceMap (g i) ≫ baseChangeSection σ hσ T := by
          have c₂ : tripleToPair₂₃ g i j k ≫ s.overlapSituation.overlapTestFst (g j) (g k) ≫ g j =
              tripleProj₁ g i j k ≫ g i := by
            rw [overlapTestHom_fst_assoc, tripleProj₂_comp, ← tripleProj₁_comp]
          rw [← Category.assoc, ← Category.assoc, ← spaceMap_comp, ← spaceMap_comp,
            Category.assoc, c₂, spaceMap_comp, Category.assoc]
        have hW₃ : spaceMap (tripleToPair₁₃ g i j k) ≫
            spaceMap (s.overlapSituation.overlapTestFst (g i) (g k)) ≫ spaceMap (g i) ≫
              baseChangeSection σ hσ T =
            spaceMap (tripleProj₁ g i j k) ≫ spaceMap (g i) ≫ baseChangeSection σ hσ T := by
          rw [← Category.assoc, ← spaceMap_comp, overlapTestHom_fst]
        have hW₁ : spaceMap (tripleToPair₁₂ g i j k) ≫
            spaceMap (s.overlapSituation.overlapTestFst (g i) (g j)) ≫ spaceMap (g i) ≫
              baseChangeSection σ hσ T =
            spaceMap (tripleProj₁ g i j k) ≫ spaceMap (g i) ≫ baseChangeSection σ hσ T := by
          rw [← Category.assoc, ← spaceMap_comp]
        have n₁ := (hψ i j).restrict σ hσ (tripleToPair₁₂ g i j k)
          (a₁' := tripleProj₁ g i j k) (a₂' := tripleProj₂ g i j k) rfl rfl hW₁
        have n₂ := (hψ j k).restrict σ hσ (tripleToPair₂₃ g i j k)
          (a₁' := tripleProj₂ g i j k) (a₂' := tripleProj₃ g i j k)
          (overlapTestHom_fst _ _ _ _ _) (overlapTestHom_snd _ _ _ _ _) hW₂
        have n₃ := (hψ i k).restrict σ hσ (tripleToPair₁₃ g i j k)
          (a₁' := tripleProj₁ g i j k) (a₂' := tripleProj₃ g i j k)
          (overlapTestHom_fst _ _ _ _ _) (overlapTestHom_snd _ _ _ _ _) hW₃
        have key := IsNormalized.eq σ hσ (hstr _) (modulePullbackInvertible _ _ (hL i))
          (n₁.trans σ hσ n₂) n₃
        have hvi : w ≫ baseChangeMap s.f (tripleProj₁ g i j k) = vi := by
          rw [baseChangeMap_comp, ← Category.assoc, ← e₁, Category.assoc,
            s.overlapSituation.overlapTestComparison_comp_baseChangeMap_fst, hij₀]
        have hvj : w ≫ baseChangeMap s.f (tripleProj₂ g i j k) = vj := by
          rw [baseChangeMap_comp, ← Category.assoc, ← e₁, Category.assoc,
            s.overlapSituation.overlapTestComparison_comp_baseChangeMap_snd, hij₁]
        have hvk : w ≫ baseChangeMap s.f (tripleProj₃ g i j k) = vk := by
          rw [← overlapTestHom_snd (g j) (g k) (tripleProj₂ g i j k) (tripleProj₃ g i j k)
              (tripleProj₂_comp g i j k), baseChangeMap_comp, ← Category.assoc, ← e₂,
            Category.assoc, s.overlapSituation.overlapTestComparison_comp_baseChangeMap_snd,
            hjk₁]
        have kc : ∀ {A B C : s.SchemesOver} (h : A ⟶ B) (p : B ⟶ C) {q : A ⟶ C}, h ≫ p = q →
            baseChangeMap s.f h ≫ baseChangeMap s.f p = baseChangeMap s.f q := by
          rintro A B C h p q rfl
          exact (baseChangeMap_comp s.f _ _).symm
        have k₁₀ := kc (tripleToPair₁₂ g i j k) (s.overlapSituation.overlapTestFst (g i) (g j))
          (q := tripleProj₁ g i j k) rfl
        have k₁₁ := kc (tripleToPair₁₂ g i j k) (s.overlapSituation.overlapTestSnd (g i) (g j))
          (q := tripleProj₂ g i j k) rfl
        have k₂₀ := kc (tripleToPair₂₃ g i j k) (s.overlapSituation.overlapTestFst (g j) (g k))
          (q := tripleProj₂ g i j k) (overlapTestHom_fst _ _ _ _ _)
        have k₂₁ := kc (tripleToPair₂₃ g i j k) (s.overlapSituation.overlapTestSnd (g j) (g k))
          (q := tripleProj₃ g i j k) (overlapTestHom_snd _ _ _ _ _)
        have k₃₀ := kc (tripleToPair₁₃ g i j k) (s.overlapSituation.overlapTestFst (g i) (g k))
          (q := tripleProj₁ g i j k) (overlapTestHom_fst _ _ _ _ _)
        have k₃₁ := kc (tripleToPair₁₃ g i j k) (s.overlapSituation.overlapTestSnd (g i) (g k))
          (q := tripleProj₃ g i j k) (overlapTestHom_snd _ _ _ _ _)
        rw [restrictPullbackIso_restrictPullbackIso_eq _ _ _ _ _ _ w _ e₁ k₁₀ k₁₁ hvi hvj,
          restrictPullbackIso_restrictPullbackIso_eq _ _ _ _ _ _ w _ e₂ k₂₀ k₂₁ hvj hvk,
          restrictPullbackIso_restrictPullbackIso_eq _ _ _ _ _ _ w _ e₃ k₃₀ k₃₁ hvi hvk,
          ← restrictPullbackIso_trans, key] }
  obtain ⟨M, hMqc, ⟨e⟩⟩ :=
    QuasiCoherentDescent.forall_isEffective_of_isFpqcCovering B S hS _ _ hcov D
  have ε : ∀ i, L i ≅ (modulePullback B S hS (baseChangeMap s.f (g i))).obj M :=
    fun i ↦ QuasiCoherentDescent.DescentDatum.appIso B S hS e i
  refine ⟨M, isInvertibleModule_of_isFpqcCovering_of_isQuasicoherentOnSite _ hcov M hMqc
    fun i ↦ ?_, fun i ↦ ⟨ε i⟩⟩
  have := hL i
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (ε i)

end PicardSituation

end AlgebraicGeometry.Space

end
