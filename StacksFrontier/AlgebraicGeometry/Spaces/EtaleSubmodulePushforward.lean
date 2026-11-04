module

import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPartRepresentable
import all StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOfOpenMorphismLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmodulePullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionStep
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietoris
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice

/-!
# Glueing submodules along étale morphisms

Let `M` be an `𝒪_X`-module on the small étale site of an algebraic space `X` and let
`f : Y ⟶ X` be étale. The restriction of submodules `N ↦ N|_Y`
(`AlgebraicGeometry.Space.etaleSubmoduleRestrict`) has a right adjoint on the lattices of
submodules, the **étale pushforward** `f_*N ⊆ M` of a submodule `N ⊆ M|_Y`: the sections of `M`
all of whose restrictions to charts of `Y` lie in `N`. It is the glued submodule
`AlgebraicGeometry.Space.etaleSubmoduleGlue` of the one-member family `f`.

Across an elementary distinguished square `(U ⊆ W, V ⟶ W)` [Stacks, Tag 08GM], submodules
`N₀ ⊆ M|_U` and `N ⊆ M|_V` agreeing over `U ×_W V` form a compatible family on the two members,
`AlgebraicGeometry.Space.EtaleSubmoduleFamily.Compatible`, so they are the restrictions of their
glued submodule (`AlgebraicGeometry.Space.etaleSubmoduleRestrict_etaleSubmoduleGlue`), which is
quasi-coherent and of finite type when they are.

## Main definitions

* `AlgebraicGeometry.Space.etaleSubmodulePushforward`: the pushforward `f_*N ⊆ M` of a
  submodule `N ⊆ M|_Y`.

## Main results

* `AlgebraicGeometry.Space.etaleSubmoduleRestrict_le_iff`: **`K|_Y ≤ N ↔ K ≤ f_*N`**, the
  adjunction between restriction and pushforward of submodules.
* `AlgebraicGeometry.Space.le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff`: the
  condition `N ≤ (f_*N')|_Y`, sectionwise.
* `AlgebraicGeometry.Space.exists_covering_eq_or_factor_of_isElementaryDistinguishedSquare` and
  `AlgebraicGeometry.Space.map_mem_of_isElementaryDistinguishedSquare`: the descent condition
  along the étale member of an elementary distinguished square follows from agreement over the
  overlap, because `V ×_W V` is covered by the diagonal and its part over `U`.
* `AlgebraicGeometry.Space.edsMemberSubmodule_compatible_of_forall`: **submodules agreeing over
  the overlap form a compatible family** on the two members.
* `AlgebraicGeometry.Space.etaleSubmoduleRestrict_edsOpenHom_etaleSubmoduleGlue`,
  `AlgebraicGeometry.Space.etaleSubmoduleRestrict_edsEtaleHom_etaleSubmoduleGlue` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_and_isFiniteTypeOnSite_etaleSubmoduleGlue`: the
  glued submodule restricts to the two pieces, and is quasi-coherent and of finite type when they
  are.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- Two composable restrictions of a presheaf of modules with the same composite agree. -/
theorem presheafOfModules_map_map_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {a b c d : Cᵒᵖ} (k : a ⟶ b) (k' : b ⟶ c) (l : a ⟶ d)
    (l' : d ⟶ c) (h : k ≫ k' = l ≫ l') (y : P.obj a) :
    P.map k' (P.map k y) = P.map l' (P.map l y) := by
  rw [← PresheafOfModules.map_comp_apply, h, PresheafOfModules.map_comp_apply]

variable {B S hS} in
/-- Transport of membership in a submodule of an étale pullback along an equality of sections
of the original module over the composite chart. -/
theorem mem_etaleSubmodule_of_eq (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS f hf).obj M).Submodule)
    {T : (smallEtaleRingedSite B S hS Y.1 Y.2).C}
    {y y' : M.val.obj (op ((ringedSitePostcomp B S hS f hf).obj T))} (e : y = y')
    (hy : y ∈ N.obj (op T)) : y' ∈ N.obj (op T) :=
  e ▸ hy

variable {B S hS} in
/-- Restriction of a section of a submodule of an étale pullback along a morphism of charts,
read on the sections of the original module over the composite charts. -/
theorem mem_etaleSubmodule_of_map_eq (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS f hf).obj M).Submodule)
    {T T' : (smallEtaleRingedSite B S hS Y.1 Y.2).C} (q : T' ⟶ T)
    {x : M.val.obj (op ((ringedSitePostcomp B S hS f hf).obj T))} (hx : x ∈ N.obj (op T))
    {y : M.val.obj (op ((ringedSitePostcomp B S hS f hf).obj T'))}
    (e : M.val.map ((ringedSitePostcomp B S hS f hf).map q).op x = y) : y ∈ N.obj (op T') :=
  e ▸ N.map_mem q.op hx

variable {B S hS}

/-! ### The pushforward of a submodule along an étale morphism -/

variable (B S hS) in
/-- **The étale pushforward `f_*N ⊆ M` of a submodule `N ⊆ M|_Y`** along an étale
`f : Y ⟶ X`: the glued submodule `AlgebraicGeometry.Space.etaleSubmoduleGlue` of the one-member
family `f`, i.e. the sections of `M` whose restriction along every morphism from the composite of
a chart of `Y` lies in `N` (`AlgebraicGeometry.Space.mem_etaleSubmodulePushforward_iff`). It is the
largest submodule of `M` whose restriction to `Y` lies in `N`
(`AlgebraicGeometry.Space.etaleSubmoduleRestrict_le_iff`). -/
def etaleSubmodulePushforward (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS f hf).obj M).Submodule) : M.Submodule :=
  etaleSubmoduleGlue B S hS (fun _ : Unit => Y) (fun _ => f) (fun _ => hf) (fun _ => N)

/-- Membership in the étale pushforward. -/
theorem mem_etaleSubmodulePushforward_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS f hf).obj M).Submodule) (Z : SmallEtale B S hS X.1)
    (x : M.val.obj (op Z)) :
    x ∈ (etaleSubmodulePushforward B S hS f hf N).obj (op Z) ↔
      ∀ (T : SmallEtale B S hS Y.1) (g : (smallEtalePostcomp B S hS f hf).obj T ⟶ Z),
        M.val.map g.op x ∈ N.obj (op T) :=
  ⟨fun h T g => h () T g, fun h _ T g => h T g⟩

/-- **Restriction and pushforward of submodules are adjoint**: `K|_Y ≤ N ↔ K ≤ f_*N`. -/
theorem etaleSubmoduleRestrict_le_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2} (K : M.Submodule)
    (N : ((etaleModulePullback B S hS f hf).obj M).Submodule) :
    etaleSubmoduleRestrict B S hS f hf K ≤ N ↔ K ≤ etaleSubmodulePushforward B S hS f hf N := by
  constructor
  · intro h Z x hx
    refine (mem_etaleSubmodulePushforward_iff f hf N Z.unop x).2 fun T g => ?_
    exact h (op T) ((mem_etaleSubmoduleRestrict_obj B S hS f hf K T _).2 (K.map_mem g.op hx))
  · intro h T x hx
    have hx' := (mem_etaleSubmoduleRestrict_obj B S hS f hf K T.unop x).1 hx
    have h' := (mem_etaleSubmodulePushforward_iff f hf N ((smallEtalePostcomp B S hS f hf).obj
      T.unop) x).1 (h (op ((smallEtalePostcomp B S hS f hf).obj T.unop)) hx') T.unop (𝟙 _)
    exact mem_etaleSubmodule_of_eq f hf N
      (moduleMap_id_apply' B S hS M ((smallEtalePostcomp B S hS f hf).obj T.unop) x) h'

/-- **The condition `N ≤ (f_*N')|_Y`, sectionwise**: a section of `N` over a chart of `Y`
restricts into `N'` along every morphism to it from the composite of a chart of `Y'`. -/
theorem le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff {Y' : AlgebraicSpaces B S hS}
    (j : Y ⟶ X) (hj : IsEtale B S hS j.hom) (f : Y' ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS j hj).obj M).Submodule)
    (N' : ((etaleModulePullback B S hS f hf).obj M).Submodule) :
    N ≤ etaleSubmoduleRestrict B S hS j hj (etaleSubmodulePushforward B S hS f hf N') ↔
      ∀ (T : (smallEtaleRingedSite B S hS Y.1 Y.2).C)
        (T' : (smallEtaleRingedSite B S hS Y'.1 Y'.2).C)
        (g : (ringedSitePostcomp B S hS f hf).obj T' ⟶ (ringedSitePostcomp B S hS j hj).obj T)
        (x : M.val.obj (op ((ringedSitePostcomp B S hS j hj).obj T))),
        x ∈ N.obj (op T) → M.val.map g.op x ∈ N'.obj (op T') := by
  constructor
  · intro h T T' g x hx
    exact (mem_etaleSubmodulePushforward_iff f hf N' ((smallEtalePostcomp B S hS j hj).obj T)
      x).1 ((mem_etaleSubmoduleRestrict_obj B S hS j hj _ T x).1 (h (op T) hx)) T' g
  · intro h T x hx
    exact (mem_etaleSubmoduleRestrict_obj B S hS j hj _ T.unop x).2
      ((mem_etaleSubmodulePushforward_iff f hf N' ((smallEtalePostcomp B S hS j hj).obj T.unop)
        x).2 fun T' g => h T.unop T' g x hx)

/-- For an étale monomorphism `j : Y ⟶ X`, for instance the inclusion of an open subspace, every
submodule `N ⊆ M|_Y` lies in the restriction of its pushforward. -/
theorem le_etaleSubmoduleRestrict_etaleSubmodulePushforward_of_mono (j : Y ⟶ X)
    (hj : IsEtale B S hS j.hom) [Mono j.hom] {M : Modules.{u, u} B S hS X.1 X.2}
    (N : ((etaleModulePullback B S hS j hj).obj M).Submodule) :
    N ≤ etaleSubmoduleRestrict B S hS j hj (etaleSubmodulePushforward B S hS j hj N) := by
  refine (le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff j hj j hj N N).2 ?_
  intro T T' g x hx
  obtain ⟨g', rfl⟩ := exists_smallEtalePostcomp_map_eq B S hS j hj inferInstance g
  exact N.map_mem g'.op hx

/-! ### Compatibility across an elementary distinguished square -/

section Square

variable {W : AlgebraicSpaces B S hS} {Ve : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : Ve ⟶ W.1}

/-- **Two charts of the étale member of an elementary distinguished square with the same image
agree locally or lie locally over the open member.** Let `T'` be an étale chart of `V` and
`b : T' ⟶ V` a second morphism with the same composite to `W`. Then `T'` is covered by charts on
which the structure morphism and `b` agree, together with charts whose composite to `W` factors
through the open subspace `U`. -/
theorem exists_covering_eq_or_factor_of_isElementaryDistinguishedSquare
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (T' : SmallEtale B S hS Ve) (b : yoneda.obj T'.1.left ⟶ Ve)
    (hb : T'.1.hom ≫ fV = b ≫ fV) :
    ∃ R ∈ SmallEtale.topology B S hS Ve T', ∀ ⦃T'' : SmallEtale B S hS Ve⦄ (p : T'' ⟶ T'), R p →
      yoneda.map p.hom.left ≫ T'.1.hom = yoneda.map p.hom.left ≫ b ∨
        ∃ c : yoneda.obj T''.1.left ⟶ Uo.toFunctor, c ≫ Uo.ι = T''.1.hom ≫ fV := by
  classical
  have hV := hsq.isAlgebraicSpace
  let a := T'.1.hom
  let pair : yoneda.obj T'.1.left ⟶ pullback fV fV := pullback.lift a b hb
  have hΔ : IsOpenImmersion B S hS (pullback.diagonal fV) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hV W.2 fV
      (isUnramified_of_isEtale B S hS hsq.isEtale)
  have hU := hsq.isOpenSubspace.2
  let X : Bool → BigFppfOver B S hS := fun
    | false => hΔ.rep.pullback pair
    | true => hU.rep.pullback (a ≫ fV)
  let u : ∀ i, X i ⟶ T'.1.left := fun
    | false => hΔ.rep.snd pair
    | true => hU.rep.snd (a ≫ fV)
  have hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (u i))
    | false => hΔ.property_snd pair
    | true => hU.property_snd (a ≫ fV)
  let Y : Bool → SmallEtale B S hS Ve := fun i =>
    ⟨CostructuredArrow.mk (yoneda.map (u i) ≫ T'.1.hom),
      etale_comp_of_scheme B S hS (u i) T'.1.hom inferInstance T'.property⟩
  let π : ∀ i, Y i ⟶ T' := fun i => ObjectProperty.homMk (CostructuredArrow.homMk (u i) rfl)
  have ha : a = pair ≫ pullback.fst fV fV := (pullback.lift_fst _ _ _).symm
  have hb' : b = pair ≫ pullback.snd fV fV := (pullback.lift_snd _ _ _).symm
  have hpts : (⋃ i, Set.range (pointsMap B S hS (yoneda.obj (X i)) (yoneda.map (u i)))) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    have hc := isEtaleCovering_overlap B S hS W.2 Uo fV hsq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1
      (hc.jointly_surjective.symm ▸ Set.mem_univ (pointsMap B S hS _ pair y))
    cases i with
    | false =>
      obtain ⟨v, hv⟩ := hi
      obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS (hΔ.rep.isPullback pair) v y hv
      exact Set.mem_iUnion.2 ⟨false, w, hw⟩
    | true =>
      obtain ⟨z, hz⟩ := hi
      have he : pointsMap B S hS _ Uo.ι
          (pointsMap B S hS _ (pullback.fst Uo.ι (pullback.fst fV fV ≫ fV)) z) =
          pointsMap B S hS _ (a ≫ fV) y := by
        have hcond := congrArg (fun k => pointsMap B S hS _ k z)
          (pullback.condition (f := Uo.ι) (g := pullback.fst fV fV ≫ fV))
        simp only [pointsMap_comp_apply] at hcond
        rw [hcond, hz, ha]
        simp only [pointsMap_comp_apply]
      obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS (hU.rep.isPullback (a ≫ fV))
        _ y he
      exact Set.mem_iUnion.2 ⟨true, w, hw⟩
  refine ⟨Sieve.ofArrows Y π, SmallEtale.ofArrows_mem_topology B S hS Ve Y π ?_, ?_⟩
  · rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
    refine ⟨fun x => ?_, fun i => inferInstanceAs (_root_.AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (u i)))⟩
    obtain ⟨i, z, hz⟩ := scheme_family_jointly_surjective_of_points B S hS X T'.1.left u hpts x
    exact ⟨i, z, hz⟩
  · intro T'' p hp
    obtain ⟨i, q, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hp
    have hq : yoneda.map q.hom.left ≫ yoneda.map (u i) ≫ T'.1.hom = T''.1.hom :=
      CostructuredArrow.w q.hom
    show yoneda.map (q.hom.left ≫ u i) ≫ a = yoneda.map (q.hom.left ≫ u i) ≫ b ∨ _
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    cases i with
    | false =>
      refine Or.inl (congrArg (yoneda.map q.hom.left ≫ ·) ?_)
      have h1 := hΔ.rep.w pair
      have key : ∀ {π : pullback fV fV ⟶ Ve} {c : yoneda.obj T'.1.left ⟶ Ve}, c = pair ≫ π →
          pullback.diagonal fV ≫ π = 𝟙 _ → yoneda.map (u false) ≫ c = hΔ.rep.fst pair := by
        intro π c hc hd
        rw [hc, ← Category.assoc]
        show (yoneda.map (hΔ.rep.snd pair) ≫ pair) ≫ π = _
        rw [← h1, Category.assoc, hd, Category.comp_id]
      exact (key ha (pullback.diagonal_fst fV)).trans (key hb' (pullback.diagonal_snd fV)).symm
    | true =>
      refine Or.inr ⟨yoneda.map q.hom.left ≫ hU.rep.fst (a ≫ fV), ?_⟩
      rw [Category.assoc, hU.rep.w, ← hq]
      simp only [Category.assoc]
      rfl

variable (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  {M : Modules.{u, u} B S hS W.1 W.2}
  (N₀ : ((etaleModulePullback B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)).obj M).Submodule)
  (N : ((etaleModulePullback B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq)).obj M).Submodule)

/-- The open member of an elementary distinguished square includes by a monomorphism. -/
instance mono_edsOpenHom_hom : Mono (edsOpenHom B S hS hsq).hom :=
  inferInstanceAs (Mono Uo.ι)

/-- **The descent condition along the étale member of an elementary distinguished square.**
Let `N₀ ⊆ M|_U` and `N ⊆ M|_V` be submodules agreeing over `U ×_W V`: restriction along a
morphism of charts of `W` from a chart of `V` to a chart of `U` carries `N₀` into `N` (`h₁`), and
from a chart of `U` to a chart of `V` carries `N` into `N₀` (`h₂`). Then restriction along any
morphism of charts of `W` between charts of `V` carries `N` into itself. -/
theorem map_mem_of_isElementaryDistinguishedSquare
    (h₁ : ∀ (T : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).C)
      (T' : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).C)
      (g : (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj T' ⟶
          (ringedSitePostcomp B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj T)
      (x : M.val.obj (op ((ringedSitePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj T))),
      x ∈ N₀.obj (op T) → M.val.map g.op x ∈ N.obj (op T'))
    (h₂ : ∀ (T : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).C)
      (T' : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).C)
      (g : (ringedSitePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj T' ⟶
          (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj T)
      (x : M.val.obj (op ((ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj T))),
      x ∈ N.obj (op T) → M.val.map g.op x ∈ N₀.obj (op T'))
    (T T' : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).C)
    (g : (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj T' ⟶
        (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)).obj T)
    (x : M.val.obj (op ((ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj T))) (hx : x ∈ N.obj (op T)) :
    M.val.map g.op x ∈ N.obj (op T') := by
  let jV := ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
  let jU := ringedSitePostcomp B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
  have hw : yoneda.map g.hom.left ≫ T.1.hom ≫ fV = T'.1.hom ≫ fV := CostructuredArrow.w g.hom
  obtain ⟨R, hR, hRp⟩ := exists_covering_eq_or_factor_of_isElementaryDistinguishedSquare hsq T'
    (yoneda.map g.hom.left ≫ T.1.hom) (hw.symm.trans (Category.assoc _ _ _).symm)
  refine N.isSheaf _ ((SmallEtale.topology B S hS Ve).superset_covering (fun T'' p hp => ?_) hR)
  show M.val.map (jV.map p).op (M.val.map g.op x) ∈ N.obj (op T'')
  have hp' : yoneda.map p.hom.left ≫ T'.1.hom = T''.1.hom := CostructuredArrow.w p.hom
  rcases hRp p hp with heq | ⟨c, hc⟩
  · let q : T'' ⟶ T := ObjectProperty.homMk (CostructuredArrow.homMk
      (p.hom.left ≫ g.hom.left)
      ((congrArg (· ≫ T.1.hom) (yoneda.map_comp _ _)).trans
        ((Category.assoc _ _ _).trans (heq.symm.trans hp'))))
    have hq : jV.map q = jV.map p ≫ g :=
      ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ rfl)
    have e : M.val.map (jV.map q).op x = M.val.map (jV.map p).op (M.val.map g.op x) := by
      rw [hq, op_comp, PresheafOfModules.map_comp_apply]
    exact mem_etaleSubmodule_of_map_eq _ _ N q hx e
  · have hcE : IsEtale B S hS c := by
      refine isEtale_of_comp_mono B S hS c Uo.ι ?_
      rw [hc]
      exact isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2 T''.property)
        hsq.isEtale
    have hc' : yoneda.map (𝟙 _) ≫ c ≫ Uo.ι = T''.1.hom ≫ fV := by simpa using hc
    have hc'' : yoneda.map (𝟙 _) ≫ T''.1.hom ≫ fV = c ≫ Uo.ι := by simpa using hc.symm
    obtain ⟨E, e₁, e₂, he₁₂⟩ : ∃ (E : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1
        (edsOpen B S hS hsq).2).C) (e₁ : jV.obj T'' ⟶ jU.obj E) (e₂ : jU.obj E ⟶ jV.obj T''),
        e₁ ≫ e₂ = 𝟙 _ :=
      ⟨⟨CostructuredArrow.mk c, (isEtale_iff_presheaf_of_yoneda B S hS c).1 hcE⟩,
        ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) hc'),
        ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _) hc''),
        ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (Category.comp_id _))⟩
    have hz := h₂ T E (e₂ ≫ jV.map p ≫ g) x hx
    have e : M.val.map e₁.op (M.val.map (e₂ ≫ jV.map p ≫ g).op x) =
        M.val.map (jV.map p).op (M.val.map g.op x) := by
      refine presheafOfModules_map_map_eq M.val _ _ _ _ ?_ x
      rw [← op_comp, ← op_comp, ← Category.assoc, he₁₂, Category.id_comp]
    exact mem_etaleSubmodule_of_eq _ _ N e (h₁ E T'' e₁ _ hz)

/-- **Submodules agreeing over the overlap of an elementary distinguished square form a compatible
family** on its two members, `AlgebraicGeometry.Space.edsMember` at the open subspace of the
square. -/
theorem edsMemberSubmodule_compatible_of_forall
    (h₁ : ∀ (T : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).C)
      (T' : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).C)
      (g : (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj T' ⟶
          (ringedSitePostcomp B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)).obj T)
      (x : M.val.obj (op ((ringedSitePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj T))),
      x ∈ N₀.obj (op T) → M.val.map g.op x ∈ N.obj (op T'))
    (h₂ : ∀ (T : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2).C)
      (T' : (smallEtaleRingedSite B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2).C)
      (g : (ringedSitePostcomp B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).obj T' ⟶
          (ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
            (isEtale_edsEtaleHom B S hS hsq)).obj T)
      (x : M.val.obj (op ((ringedSitePostcomp B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).obj T))),
      x ∈ N.obj (op T) → M.val.map g.op x ∈ N₀.obj (op T')) :
    EtaleSubmoduleFamily.Compatible B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀ N) := by
  rintro ⟨_ | _⟩ ⟨_ | _⟩ V V' φ t ht
  · exact map_mem_of_isElementaryDistinguishedSquare hsq N₀ N h₁ h₂ V' V φ t ht
  · exact h₁ V' V φ t ht
  · exact h₂ V' V φ t ht
  · obtain ⟨φ', rfl⟩ := exists_smallEtalePostcomp_map_eq B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) inferInstance φ
    exact N₀.map_mem φ'.op ht

/-- **The two members of an elementary distinguished square form an étale covering** of its
target: every point lies on the open subspace or in the image of the étale morphism. The
family is `AlgebraicGeometry.Space.edsMember` at the open subspace of the square itself. -/
theorem isEtaleCovering_edsMember :
    IsEtaleCovering B S hS (fun i => (edsMember B S hS hsq Uo hsq.isOpenSubspace i).1)
      (fun i => (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace i).hom) :=
  ⟨W.2, fun i => (edsMember B S hS hsq Uo hsq.isOpenSubspace i).2,
    isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace,
    Set.eq_univ_of_forall fun x => by
      rcases points_covered_by_open_or_etale B S hS W.2 Uo fV hsq x with hx | ⟨y, hy⟩
      · exact Set.mem_iUnion.2 ⟨⟨true⟩, hx⟩
      · exact Set.mem_iUnion.2 ⟨⟨false⟩, y, hy⟩⟩

/-- **Submodules agreeing over the overlap form a compatible family**, the agreement stated as
`N₀ ≤ (j_{V,*}N)|_U` and `N ≤ (j_{U,*}N₀)|_V`; the sectionwise form is
`AlgebraicGeometry.Space.edsMemberSubmodule_compatible_of_forall`. -/
theorem edsMemberSubmodule_compatible_of_le
    (h₁ : N₀ ≤ etaleSubmoduleRestrict B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) N))
    (h₂ : N ≤ etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) N₀)) :
    EtaleSubmoduleFamily.Compatible B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀ N) :=
  edsMemberSubmodule_compatible_of_forall hsq N₀ N
    ((le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff _ _ _ _ N₀ N).1 h₁)
    ((le_etaleSubmoduleRestrict_etaleSubmodulePushforward_iff _ _ _ _ N N₀).1 h₂)

/-- **The glued submodule restricts to `N₀` on the open member** when `N₀` and `N` agree over the
overlap, in the form `N₀ ≤ (j_{V,*}N)|_U` and `N ≤ (j_{U,*}N₀)|_V`. -/
theorem etaleSubmoduleRestrict_edsOpenHom_etaleSubmoduleGlue
    (h₁ : N₀ ≤ etaleSubmoduleRestrict B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) N))
    (h₂ : N ≤ etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) N₀)) :
    etaleSubmoduleRestrict B S hS (edsOpenHom B S hS hsq) (isEtale_edsOpenHom B S hS hsq)
      (etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀ N)) = N₀ :=
  etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _
    (edsMemberSubmodule_compatible_of_le hsq N₀ N h₁ h₂) ⟨true⟩

/-- **The glued submodule restricts to `N` on the étale member** when `N₀` and `N` agree over the
overlap. -/
theorem etaleSubmoduleRestrict_edsEtaleHom_etaleSubmoduleGlue
    (h₁ : N₀ ≤ etaleSubmoduleRestrict B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) N))
    (h₂ : N ≤ etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) N₀)) :
    etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq) (isEtale_edsEtaleHom B S hS hsq)
      (etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀ N)) = N :=
  etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _
    (edsMemberSubmodule_compatible_of_le hsq N₀ N h₁ h₂) ⟨false⟩

/-- **The submodule glued across an elementary distinguished square is quasi-coherent and of
finite type** when the two pieces are and agree over the overlap. -/
theorem isQuasicoherentOnSite_and_isFiniteTypeOnSite_etaleSubmoduleGlue
    (h₁ : N₀ ≤ etaleSubmoduleRestrict B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) N))
    (h₂ : N ≤ etaleSubmoduleRestrict B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq) (etaleSubmodulePushforward B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) N₀))
    (hN₀q : N₀.toSheafOfModules.IsQuasicoherentOnSite)
    (hN₀f : N₀.toSheafOfModules.IsFiniteTypeOnSite)
    (hNq : N.toSheafOfModules.IsQuasicoherentOnSite)
    (hNf : N.toSheafOfModules.IsFiniteTypeOnSite) :
    (etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
      (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀
        N)).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleGlue B S hS (edsMember B S hS hsq Uo hsq.isOpenSubspace)
        (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
        (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
        (edsMemberSubmodule B S hS hsq Uo hsq.isOpenSubspace N₀
          N)).toSheafOfModules.IsFiniteTypeOnSite := by
  have hcomp := edsMemberSubmodule_compatible_of_le hsq N₀ N h₁ h₂
  obtain ⟨hq, hf⟩ := isQuasicoherentOnSite_isFiniteType_of_etaleSubmoduleRestrict B S hS
    (edsMember B S hS hsq Uo hsq.isOpenSubspace) (edsMemberHom B S hS hsq Uo hsq.isOpenSubspace)
    (isEtale_edsMemberHom B S hS hsq Uo hsq.isOpenSubspace) (isEtaleCovering_edsMember hsq) _
    fun i => by
      rw [etaleSubmoduleRestrict_etaleSubmoduleGlue B S hS _ _ _ _ hcomp i]
      rcases i with ⟨_ | _⟩
      · exact ⟨hNq, Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hNf⟩
      · exact ⟨hN₀q, Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ hN₀f⟩
  exact ⟨hq, Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ hf⟩

end Square

end AlgebraicGeometry.Space

end
