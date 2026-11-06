module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.LocallyConstantComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.ConstantAdicQuotientTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Values of locally constant sheaves of modules on the small pro-étale site

Let `Λ` be a ring and `X` a scheme. This file collects three facts about the constant values of
a locally constant sheaf of `Λ`-modules on `X_proét`.

* If the sheaf is moreover constructible and `Λ` is Noetherian, its constant values are finitely
  generated: a locally constant constructible sheaf is locally constant of finite type.
  In particular a constructible constant sheaf `M̲` on a nonempty scheme has `M` finitely
  generated.
* If the sheaf is locally constant of finite presentation and `X` is connected, all its constant
  values over nonempty objects are isomorphic to one module `M` (the pro-étale form of
  Stacks 09BF): the sets of points of `X` over which the value is a given module are open,
  because the sheaf is already étale locally constant, and they partition `X`.
* Consequently such a sheaf is locally isomorphic to the constant sheaf `M̲`, and it is
  isomorphic to `M̲` over every affine object whose ring of global sections is w-contractible.

## Main results

* `AlgebraicGeometry.ProEtale.isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant`:
  locally constant and constructible implies locally constant of finite type.
* `AlgebraicGeometry.ProEtale.finite_of_isConstructibleModuleSheaf'_constantSheaf`: a
  constructible constant sheaf on a nonempty scheme has a finitely generated value.
* `AlgebraicGeometry.ProEtale.exists_forall_nonempty_linearEquiv_of_connectedSpace`: on a
  connected scheme the constant values of a locally constant sheaf of finite presentation are
  all isomorphic.
* `AlgebraicGeometry.ProEtale.isZero_of_isZero_overPullback_of_connectedSpace`: on a connected
  scheme such a sheaf vanishing over one nonempty object vanishes.
* `AlgebraicGeometry.ProEtale.nonempty_overPullback_iso_constantSheaf_of_isWContractible`: such
  a sheaf is the constant sheaf `M̲` over a w-contractible affine object.

## References

* [Stacks Project, Tag 09BF](https://stacks.math.columbia.edu/tag/09BF)
* [Stacks Project, Tag 09BW](https://stacks.math.columbia.edu/tag/09BW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} (Λ : Type v) [CommRing Λ]

attribute [local instance] hasSheafify_proEt_over_moduleCat'
  wEqualsLocallyBijective_proEt_over_moduleCat

/-- On the pro-étale site of `Y` localized at `U`, composing a sheaf of `R`-modules with the
forgetful functor to types yields a sheaf. -/
local instance hasSheafCompose_proEt_over_moduleCat (R : Type v) [CommRing R]
    {Y : Scheme.{u}} (U : Y.ProEt) :
    ((Scheme.ProEt.topology Y).over U).HasSheafCompose
      (forget (ModuleCat.{max (u + 1) v w} R)) :=
  inferInstance

/-- A sieve on `T` lies in the pro-étale topology once it contains, over every nonempty object
mapping to a member of a covering family, the corresponding arrow. -/
private theorem mem_proEt_topology_of_forall_nonempty {T : X.ProEt} {I : Type*} {V : I → X.ProEt}
    {f : ∀ i, V i ⟶ T} (hf : Sieve.ofArrows V f ∈ Scheme.ProEt.topology X T) (R : Sieve T)
    (h : ∀ i {Z : X.ProEt} (q : Z ⟶ V i), Nonempty Z.left → R (q ≫ f i)) :
    R ∈ Scheme.ProEt.topology X T := by
  refine (Scheme.ProEt.topology X).transitive hf _ fun Z g hg => ?_
  obtain ⟨i, k, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  by_cases hZ : Nonempty Z.left
  · exact (Scheme.ProEt.topology X).superset_covering
      (fun _ q _ => show R.arrows (q ≫ k ≫ f i) from Sieve.downward_closed _ (h i k hZ) q)
      ((Scheme.ProEt.topology X).top_mem Z)
  · exact (Scheme.ProEt.topology X).superset_covering bot_le
      (Scheme.ProEt.bot_mem_topology_of_isEmpty Z (not_nonempty_iff.mp hZ))

/-- **The values of a locally constant constructible sheaf are finitely generated.** Over a
Noetherian ring, a locally constant sheaf of modules on `X_proét` which is constructible is
locally constant of finite type.

Let `G|_V ≅ N̲` with `V` nonempty. A point of `V` lies over a point `x` of `X`, which lies on a
stratum `ι : P → X` of a stratification of an affine neighbourhood along which `ι⁻¹G` is locally
constant of finite type. The inverse image of `G|_V ≅ N̲` is `ι⁻¹G|_{V ×_X P} ≅ N̲`, and
`V ×_X P` is nonempty, so on a nonempty member of a trivializing covering of `ι⁻¹G` the constant
sheaf `N̲` is isomorphic to the constant sheaf of a finitely generated module; then `N` is
finitely generated (`Stacks.ConstantSheaf.finite_of_constantSheaf_iso`). -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant [IsNoetherianRing Λ]
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    [hl : IsLocallyConstant (Scheme.ProEt.topology X) G]
    (hG : IsConstructibleModuleSheaf'.{u, v, w} X Λ G) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology X) Λ G := by
  rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) v w} Λ
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  obtain ⟨I, V, f, hf, hc⟩ := hl.exists_cover T
  -- keep the members with a point; the empty ones are covered by the empty sieve
  let I' := {i : I // Nonempty (V i).left}
  have hf' : Sieve.ofArrows (fun i : I' => V i.1) (fun i => f i.1) ∈ J T :=
    mem_proEt_topology_of_forall_nonempty hf _ fun i Z q ⟨z⟩ =>
      Sieve.downward_closed _ (Sieve.ofArrows_mk
        (fun i : I' => V i.1) (fun i => f i.1) ⟨i, ⟨q.left z⟩⟩) q
  refine isFinitePresentationLocallyConstantModuleSheaf_of_cover J Λ (isTerminalProEtId X) G hf'
    fun i => ?_
  obtain ⟨y⟩ := i.2
  obtain ⟨N, ⟨c⟩⟩ := (hc i.1).mem_essImage
  -- a stratum through the image of `y`
  let x : X := (V i.1).hom.base y
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨s, hs⟩ := hG ⟨U, hU⟩
  obtain ⟨k, p, hp⟩ : ∃ k, x ∈ Set.range (s.inclusion k).base := by
    have : x ∈ (⋃ k, Set.range (s.inclusion k).base) := s.covers ▸ hxU
    simpa using this
  let ι := s.inclusion k
  let bc := Scheme.proetaleBaseChange ι
  let K := Scheme.ProEt.topology (s.piece k)
  let H := (proetaleModuleInverseImage.{u, v, w} ι Λ).obj G
  have hH : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v} K Λ H := hs k
  -- `H` restricted to `V ×_X P` is the constant sheaf on `N`
  have (U : (s.piece k).ProEt) : HasSheafify (K.over U) A :=
    hasSheafify_moduleCat.{u + 1, u, max v w, v} _ _
  let c' : (constantSheaf (K.over (bc.obj (V i.1))) A).obj N ≅
      (K.overPullback A (bc.obj (V i.1))).obj H :=
    constantIsoOverPullbackSheafPullback J K A bc (V i.1) G N c ≪≫
      (K.overPullback A (bc.obj (V i.1))).mapIso
        ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} Λ ι).app G).symm
  -- a point of `V ×_X P`
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y p hp.symm
  obtain ⟨I₂, Z, g, hg, hZ⟩ := hH (bc.obj (V i.1))
  obtain ⟨Z', g', hg', hz⟩ := Scheme.ProEt.exists_mem_range_of_mem_topology hg z
  obtain ⟨m, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg'
  obtain ⟨z', -⟩ := hz
  obtain ⟨E, hE, ⟨e⟩⟩ := hZ m
  have hEf : Module.Finite Λ E := (ModuleCat.isFG_iff _).mp hE
  have := Module.finitePresentation_of_finite Λ E
  have hN : Module.Finite Λ N :=
    finite_of_constantSheaf_iso.{u + 1, u, v, max (u + 1) v w} (K.over (Z m))
      (Scheme.ProEt.exists_bot_notMem_over (h.left z')) E N
      (e ≪≫ (constantIsoOverPullbackOfMap K A (g m) H N c').symm)
  exact ⟨N, Module.finitePresentation_of_finite Λ N, ⟨c⟩⟩

/-- **Stacks 09BF on the pro-étale site.** On a connected scheme `X`, the constant values of a
locally constant sheaf of finite presentation on `X_proét` over nonempty objects are all
isomorphic to one finitely presented module `M`.

The sheaf is already étale locally constant
(`AlgebraicGeometry.ProEtale.exists_covering_iso_constantSheaf`): it is constant with a value
`M k` over the members `Z k` of an étale covering of `X`. Values over objects with points of the
same image are isomorphic (`AlgebraicGeometry.ProEtale.nonempty_linearEquiv_of_apply_eq`), so
the images of the `Z k` with value isomorphic to `M k₀`, and those of the others, are two
disjoint open subsets covering `X`; as `X` is connected the second is empty. -/
theorem exists_forall_nonempty_linearEquiv_of_connectedSpace [ConnectedSpace X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F) :
    ∃ M : ModuleCat.{max (u + 1) v w} Λ, Module.FinitePresentation Λ M ∧
      ∀ (Y : X.ProEt) (N : ModuleCat.{max (u + 1) v w} Λ) [Module.FinitePresentation Λ N],
        ((constantSheaf ((Scheme.ProEt.topology X).over Y) (ModuleCat.{max (u + 1) v w} Λ)).obj N ≅
          ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y).obj F) →
        Y.left → Nonempty ((N : Type (max (u + 1) v w)) ≃ₗ[Λ] (M : Type (max (u + 1) v w))) := by
  classical
  obtain ⟨S, hS, hs⟩ := exists_covering_iso_constantSheaf Λ F hF (etaleFinal X)
  obtain ⟨K, Z, p, hp⟩ := S.exists_eq_ofArrows
  have hpz (k : K) : (p k).left = (Z k).hom :=
    (Category.comp_id _).symm.trans (MorphismProperty.Over.w (p k))
  have hcov : ∀ x : X, ∃ k, x ∈ Set.range (Z k).hom := by
    intro x
    rw [hp] at hS
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp hS
    have hx : x ∈ ⋃ k, Set.range (p k).left := h ▸ Set.mem_univ x
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact ⟨k, hpz k ▸ hk⟩
  have hmem (k : K) : S (p k) := by rw [hp]; exact Sieve.ofArrows_mk Z p k
  choose M hM c using fun k => hs (hmem k)
  -- two trivializations over points with the same image in `X` have isomorphic values
  have key : ∀ (Y₁ Y₂ : X.ProEt) (N₁ N₂ : ModuleCat.{max (u + 1) v w} Λ)
      [Module.FinitePresentation Λ N₁] [Module.FinitePresentation Λ N₂],
      ((constantSheaf ((Scheme.ProEt.topology X).over Y₁) _).obj N₁ ≅
        ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y₁).obj F) →
      ((constantSheaf ((Scheme.ProEt.topology X).over Y₂) _).obj N₂ ≅
        ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y₂).obj F) →
      ∀ (y₁ : Y₁.left) (y₂ : Y₂.left), Y₁.hom y₁ = Y₂.hom y₂ →
        Nonempty ((N₁ : Type (max (u + 1) v w)) ≃ₗ[Λ] (N₂ : Type (max (u + 1) v w))) := by
    intro Y₁ Y₂ N₁ N₂ _ _ c₁ c₂ y₁ y₂ h
    refine nonempty_linearEquiv_of_apply_eq Λ ((isTerminalProEtId X).from Y₁)
      ((isTerminalProEtId X).from Y₂) F N₁ N₂ c₁ c₂ y₁ y₂ ?_
    have hw (Y : X.ProEt) : ((isTerminalProEtId X).from Y).left = Y.hom :=
      (Category.comp_id _).symm.trans (MorphismProperty.Over.w ((isTerminalProEtId X).from Y))
    rw [hw, hw]
    exact h
  have : ∀ k, Module.FinitePresentation Λ (M k) := hM
  have hkey (k l : K) (x : X) (hk : x ∈ Set.range (Z k).hom) (hl : x ∈ Set.range (Z l).hom) :
      Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M l : Type (max (u + 1) v w))) := by
    obtain ⟨z, hz⟩ := hk
    obtain ⟨z', hz'⟩ := hl
    exact key (X.etaleToProetale.obj (Z k)) (X.etaleToProetale.obj (Z l)) (M k) (M l)
      (c k).some (c l).some z z' (hz.trans hz'.symm)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨k₀, hk₀⟩ := hcov x₀
  let P : K → Prop := fun k =>
    Nonempty ((M k : Type (max (u + 1) v w)) ≃ₗ[Λ] (M k₀ : Type (max (u + 1) v w)))
  let T₁ : Set X := ⋃ (k : K) (_ : P k), Set.range (Z k).hom
  let T₂ : Set X := ⋃ (k : K) (_ : ¬ P k), Set.range (Z k).hom
  have hO (k : K) : IsOpen (Set.range (Z k).hom) := (Z k).hom.isOpenMap.isOpen_range
  have hT₁ : IsOpen T₁ := isOpen_iUnion fun k => isOpen_iUnion fun _ => hO k
  have hT₂ : IsOpen T₂ := isOpen_iUnion fun k => isOpen_iUnion fun _ => hO k
  have hcompl : T₁ᶜ = T₂ := by
    ext x
    simp only [T₁, T₂, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hcov x
      exact ⟨k, fun hPk => hx k hPk hk, hk⟩
    · rintro ⟨l, hl, hxl⟩ k hPk hxk
      obtain ⟨e⟩ := hkey l k x hxl hxk
      exact hl ⟨e.trans hPk.some⟩
  have hclopen : IsClopen T₁ := ⟨by rwa [← isOpen_compl_iff, hcompl], hT₁⟩
  have huniv : T₁ = Set.univ :=
    hclopen.eq_univ ⟨x₀, Set.mem_iUnion.mpr ⟨k₀, Set.mem_iUnion.mpr ⟨⟨LinearEquiv.refl _ _⟩, hk₀⟩⟩⟩
  refine ⟨M k₀, hM k₀, fun Y N _ cY y => ?_⟩
  have hx : Y.hom y ∈ T₁ := huniv ▸ Set.mem_univ _
  obtain ⟨k, hPk, z, hz⟩ : ∃ k, P k ∧ Y.hom y ∈ Set.range (Z k).hom := by
    simpa [T₁] using hx
  obtain ⟨e⟩ := key Y (X.etaleToProetale.obj (Z k)) N (M k) cY (c k).some y z hz.symm
  exact ⟨e.trans hPk.some⟩

/-- **On a connected scheme a locally constant sheaf vanishing over one nonempty object
vanishes.** All constant values of a locally constant sheaf of finite presentation on a
connected `X` over nonempty objects are isomorphic to one module `M`
(`exists_forall_nonempty_linearEquiv_of_connectedSpace`); the value over `V` is zero, so `M` is
zero, and the sheaf vanishes over the nonempty members of each trivializing covering, while its
sections over an empty object vanish anyway. -/
theorem isZero_of_isZero_overPullback_of_connectedSpace [ConnectedSpace X]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F)
    {V : X.ProEt} (y : V.left)
    (hV : IsZero (((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) V).obj
      F)) :
    IsZero F := by
  classical
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) v w} Λ
  obtain ⟨M, hM, hMv⟩ := exists_forall_nonempty_linearEquiv_of_connectedSpace Λ F hF
  let Z : A := ModuleCat.of Λ PUnit
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  have hadd (W : X.ProEt) : (constantSheaf (J.over W) A).Additive := by
    unfold constantSheaf
    infer_instance
  obtain ⟨eM⟩ := hMv V Z (((constantSheaf (J.over V) A).map_isZero hZ).iso hV) y
  have : Subsingleton M := eM.symm.toEquiv.subsingleton
  -- sections over every object vanish
  have hobj : ∀ U : X.ProEt, IsZero (F.obj.obj (op U)) := by
    intro U
    obtain ⟨I, W, f, hW, hc⟩ := hF U
    rw [IsZero.iff_id_eq_zero]
    refine ((F.property (F.obj.obj (op U))) _ hW).isSeparatedFor.ext fun W' g hg => ?_
    refine IsZero.eq_of_tgt ?_ _ _
    obtain ⟨_, a, _, ⟨i⟩, rfl⟩ := hg
    rcases isEmpty_or_nonempty (W i).left with he | hne
    · rw [IsZero.iff_id_eq_zero]
      exact ((F.property (F.obj.obj (op W'))) _ (Scheme.ProEt.bot_mem_topology_of_isEmpty W'
        ⟨fun w' => he.false (a.left w')⟩)).isSeparatedFor.ext fun _ _ h => h.elim
    · obtain ⟨wi⟩ := hne
      obtain ⟨E, hE, ⟨c⟩⟩ := hc i
      obtain ⟨eE⟩ := hMv (W i) E c wi
      have hEz : IsZero E := by
        have : Subsingleton E := eE.toEquiv.subsingleton
        exact ModuleCat.isZero_of_subsingleton E
      have hcE : IsZero ((J.overPullback A (W i)).obj F) :=
        ((constantSheaf (J.over (W i)) A).map_isZero hEz).of_iso c.symm
      exact ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Over.mk a))).map_isZero hcE :)
  rw [IsZero.iff_id_eq_zero]
  ext U : 3
  exact (hobj U.unop).eq_of_src _ _

/-- **A locally constant sheaf with one value is constant over a w-contractible affine.** Let
`F` be locally constant of finite presentation on `X_proét`, with all its constant values over
nonempty objects isomorphic to `M`. Over an affine object `W` whose ring of global sections is
w-contractible, `F` is isomorphic to the constant sheaf `M̲`: it is locally isomorphic to `M̲`,
and over `W` local isomorphisms glue
(`Stacks.ConstantSheaf.nonempty_overPullback_iso_of_mem`), because sections over `W` are exact
(`AlgebraicGeometry.Scheme.ProEt.surjective_app_of_isWContractible`). -/
theorem nonempty_overPullback_iso_constantSheaf_of_isWContractible
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, v, max v w}
      (Scheme.ProEt.topology X) Λ F)
    (M : ModuleCat.{max (u + 1) v w} Λ)
    (hval : ∀ (Y : X.ProEt) (N : ModuleCat.{max (u + 1) v w} Λ) [Module.FinitePresentation Λ N],
        ((constantSheaf ((Scheme.ProEt.topology X).over Y) (ModuleCat.{max (u + 1) v w} Λ)).obj N ≅
          ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) Y).obj F) →
        Y.left → Nonempty ((N : Type (max (u + 1) v w)) ≃ₗ[Λ] (M : Type (max (u + 1) v w))))
    (W : X.ProEt) [IsAffine W.left]
    (hW : ProetaleWContractible.IsWContractible.{u, u} Γ(W.left, ⊤)) :
    Nonempty ((constantSheaf ((Scheme.ProEt.topology X).over W)
        (ModuleCat.{max (u + 1) v w} Λ)).obj M ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) v w} Λ) W).obj F) := by
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) v w} Λ
  let R : Sieve W :=
    { arrows := fun V _ =>
        Nonempty ((constantSheaf (J.over V) A).obj M ≅ (J.overPullback A V).obj F)
      downward_closed := fun {V V'} _ ⟨c⟩ g => ⟨constantIsoOverPullbackOfMap J A g F M c⟩ }
  have hR : R ∈ J W := by
    obtain ⟨I, V, f, hf, hV⟩ := hF W
    refine mem_proEt_topology_of_forall_nonempty hf R fun i Z q ⟨z⟩ => ?_
    obtain ⟨E, hE, ⟨c⟩⟩ := hV i
    obtain ⟨e⟩ := hval (V i) E c (q.left z)
    exact ⟨constantIsoOverPullbackOfMap J A q F M
      ((constantSheaf (J.over (V i)) A).mapIso (LinearEquiv.toModuleIso e).symm ≪≫ c)⟩
  obtain ⟨e⟩ := nonempty_overPullback_iso_of_mem J A
    (fun φ hφ => Scheme.ProEt.surjective_app_of_isWContractible W hW φ hφ) hR
    (F := (constantSheaf J A).obj M) (G := F)
    fun V _ ⟨c⟩ => ⟨((overPullbackConstantSheafIso J A V).app M).symm ≪≫ c⟩
  exact ⟨(overPullbackConstantSheafIso J A W).app M ≪≫ e⟩

end AlgebraicGeometry.ProEtale

end
