module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.DescentFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Etale.UnramifiedTopological.Sections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedImmersionsPushforward.LiftingMorphisms
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.LocallyClosed

/-!
# Clopen branches of pullbacks and gluing over étale covers

Auxiliary results for `AlgebraicGeometry.SmallEtale.supportedSectionsEquiv`: the section of
the pullback of a closed immersion along an étale morphism selects an open-and-closed branch,
the open `selectedBranchOpen` cutting out that branch, the bound
`AlgebraicGeometry.SmallEtale.supportSection_restrict_subset_preimage` on the support of a
restricted section, and the separation and gluing of sections over a jointly surjective
family of étale maps in the small étale site.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

/-- In the pullback of a closed immersion along an étale morphism, a section
whose composite is also a closed immersion selects an open-and-closed branch. -/
private theorem pullback_section_range_isClopen {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale f] [IsClosedImmersion g]
    (i : Z ⟶ X) (h : i ≫ f = g) [IsClosedImmersion i] :
    IsClopen (Set.range
      (pullback.lift i (𝟙 Z) (by simpa [h])).base) := by
  let j : Z ⟶ pullback f g := pullback.lift i (𝟙 Z) (by simp [h])
  have hjf : j ≫ pullback.fst f g = i := pullback.lift_fst _ _ _
  have hjs : j ≫ pullback.snd f g = 𝟙 Z := pullback.lift_snd _ _ _
  have hopen : IsOpenImmersion j := AlgebraicGeometry.Unramified.section_isOpenImmersion
    (pullback.snd f g) j hjs
  have hclosed : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ pullback.fst f g) := by
      rw [hjf]
      infer_instance
    exact IsClosedImmersion.of_comp j (pullback.fst f g)
  exact ⟨hclosed.isClosedEmbedding.isClosed_range, hopen.isOpen_range⟩

/-- The other part of the inverse image of a closed support is closed in the
étale source. -/
private theorem pullback_extra_branch_isClosed {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale f] [IsClosedImmersion g]
    (i : Z ⟶ X) (h : i ≫ f = g) [IsClosedImmersion i] :
    IsClosed (Set.range (pullback.fst f g).base \ Set.range i.base) := by
  let j : Z ⟶ pullback f g := pullback.lift i (𝟙 Z) (by simp [h])
  have hjf : j ≫ pullback.fst f g = i := pullback.lift_fst _ _ _
  have hclopen : IsClopen (Set.range j.base) :=
    pullback_section_range_isClopen f g i h
  have hrange : Set.image (pullback.fst f g).base (Set.range j.base) =
      Set.range i.base := by
    have hbase : (pullback.fst f g).base ∘ j.base = i.base := by
      funext x
      exact congrArg (fun k : Z ⟶ X => k.base x) hjf
    rw [← Set.range_comp, hbase]
  have hdiff : Set.range (pullback.fst f g).base \ Set.range i.base =
      Set.image (pullback.fst f g).base (Set.range j.base)ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, hnot⟩
      exact ⟨y, fun hy => hnot (hrange ▸ ⟨y, hy, rfl⟩), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      intro hx
      rw [← hrange] at hx
      obtain ⟨z, hz, hzy⟩ := hx
      exact hy ((IsClosedImmersion.isClosedEmbedding (pullback.fst f g)).injective hzy ▸ hz)
  rw [hdiff]
  exact (IsClosedImmersion.isClosedEmbedding (pullback.fst f g)).isClosedMap
    _ hclopen.2.isClosed_compl

/-- Restricting a section along an arrow of the small étale site shrinks its support into the
inverse image of the original support. -/
public theorem supportSection_restrict_subset_preimage
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U U' : SmallEtale B S hS) (f : U' ⟶ U) (s : F.obj.obj (op U)) :
    supportSection B S hS F U'
        (F.obj.map f.op s) ⊆
      Set.preimage ((SmallEtale.toScheme B S hS).map f).base
        (supportSection B S hS F U s) := by
  let g := (SmallEtale.toScheme B S hS).map f
  have hzeroOpen :
      Set.preimage g.base
          (zeroOpen B S hS F U s :
            Set ((SmallEtale.toScheme B S hS).obj U)) ⊆
        (zeroOpen B S hS F U' (F.obj.map f.op s) :
          Set ((SmallEtale.toScheme B S hS).obj U')) := by
    intro x hx
    let W : ((SmallEtale.toScheme B S hS).obj U').Opens :=
      ⟨g.base ⁻¹' (zeroOpen B S hS F U s :
        Set ((SmallEtale.toScheme B S hS).obj U)),
        (zeroOpen B S hS F U s).2.preimage g.continuous⟩
    have hxW : x ∈ W := hx
    let V := openObject B S hS U' W
    let j := openObjectι B S hS U' W
    have hjmap : (SmallEtale.toScheme B S hS).map j = W.ι :=
      openObjectι_map B S hS U' W
    have : IsOpenImmersion ((SmallEtale.toScheme B S hS).map j) :=
      hjmap ▸ (inferInstance : IsOpenImmersion W.ι)
    have hjrange : Set.range ((SmallEtale.toScheme B S hS).map j).base = W :=
      openObjectι_range B S hS U' W
    have hcompImage : Set.range (((SmallEtale.toScheme B S hS).map (j ≫ f)).base) ⊆
        (zeroOpen B S hS F U s :
          Set ((SmallEtale.toScheme B S hS).obj U)) := by
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      show g.base (((SmallEtale.toScheme B S hS).map j).base z) ∈ _
      have hmem : ((SmallEtale.toScheme B S hS).map j).base z ∈
          (W : Set ((SmallEtale.toScheme B S hS).obj U')) :=
        hjrange ▸ Set.mem_range_self z
      show ((SmallEtale.toScheme B S hS).map j).base z ∈
        g.base ⁻¹' (zeroOpen B S hS F U s : Set _)
      exact hmem
    have hzero : F.obj.map (j ≫ f).op s = 0 :=
      (map_eq_zero_iff_range_subset_zeroOpen B S hS F U s V (j ≫ f)).2 hcompImage
    have hW : (W : Set ((SmallEtale.toScheme B S hS).obj U')) ⊆
        (zeroOpen B S hS F U' (F.obj.map f.op s) :
          Set ((SmallEtale.toScheme B S hS).obj U')) := by
      unfold zeroOpen
      show W ≤ sSup {W | IsZeroOpen
        B S hS F U' (F.obj.map f.op s) W}
      exact le_sSup ⟨V, j, inferInstance, hjrange.symm,
        by simpa [Functor.map_comp, Category.assoc] using hzero⟩
    exact hW hxW
  intro x hx
  change x ∉ (zeroOpen B S hS F U'
      (F.obj.map f.op s) : Set _) at hx
  show g.base x ∉
    (zeroOpen B S hS F U s : Set _)
  intro hx'
  exact hx (hzeroOpen hx')

private theorem presieve_map_injective_of_injective_obj
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (hobj : Function.Injective F.obj) [F.Faithful]
    {X : C} {R Q : Presieve X}
    (h : R.map F = Q.map F) : R = Q := by
  have key : ∀ {R Q : Presieve X}, R.map F = Q.map F → ∀ {Y} {g : Y ⟶ X}, R g → Q g := by
    intro R Q h Y g hg
    have hm : (R.map F) (F.map g) := Presieve.map_map hg
    rw [h, Presieve.map_iff] at hm
    obtain ⟨Z, hZ, a, ha, hfac⟩ := hm
    cases hobj hZ
    have hfac' : a = g := F.map_injective (by simpa using hfac)
    simpa [hfac'] using ha
  funext Y g
  exact propext ⟨key h, key h.symm⟩

private theorem smallEtale_cover_of_jointlySurjective_etale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : SmallEtale B S hS} {I : Type (u + 1)}
    (Y : I → SmallEtale B S hS) (f : ∀ i, Y i ⟶ X)
    (hcover : ∀ x : ((SmallEtale.toScheme B S hS).obj X),
      ∃ i y, ((SmallEtale.toScheme B S hS).map (f i)).base y = x)
    (hetale : ∀ i, Etale ((SmallEtale.toScheme B S hS).map (f i))) :
    Sieve.generate (Presieve.ofArrows Y f) ∈
      SmallEtale.topology B S hS X := by
  let E : PreZeroHypercover X := ⟨I, Y, f⟩
  let H₀ := SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)
  let H : SmallEtale B S hS ⥤ Scheme.{u} :=
    SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS) ⋙ B.inclusion
  have hscheme : (E.map H).presieve₀ ∈
      Scheme.etalePrecoverage (H.obj X) := by
    show Presieve.ofArrows _ _ ∈ Scheme.precoverage (fun _ _ f => Etale f) (H.obj X)
    rw [Scheme.ofArrows_mem_precoverage_iff
      (P := fun _ _ f => Etale f)]
    exact ⟨hcover, hetale⟩
  let ECover : Covering.{u + 1, u, u + 1} B.Scheme :=
    ⟨(Over.forget (B.obj S hS)).obj ((SmallEtale.inclusion B S hS).obj X), E.map H₀⟩
  have hECover : IsEtaleCovering ECover := hscheme
  obtain ⟨V, hV, hcomb⟩ := B.exists_covering_rep ECover hECover
  rcases V with ⟨Vtarget, Vfamily⟩
  obtain ⟨hXV, hcomb⟩ := hcomb
  cases hXV
  have hVmem : (Vfamily.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj (H₀.obj X)) := hV.1
  have hVEtale (i : Vfamily.I₀) : Etale (B.inclusion.map (Vfamily.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := fun _ _ f => Etale f)).mp hVmem).2 i
  let E' : PreZeroHypercover X :=
      ⟨Vfamily.I₀,
      fun i => ⟨Over.mk (Vfamily.f i ≫ X.obj.hom), by
        show Etale (B.inclusion.map (Vfamily.f i ≫ X.obj.hom))
        rw [Functor.map_comp]
        let := hVEtale i
        let := X.property
        infer_instance⟩,
      fun i => CategoryTheory.ObjectProperty.homMk
        (Over.homMk (Vfamily.f i))⟩
  have hselected : SmallEtale.IsCovering B S hS ⟨X, E'⟩ := by
    show B.IsCovering
      ⟨H₀.obj X, (E'.map (SmallEtale.inclusion B S hS)).map
        (Over.forget (B.obj S hS))⟩
    have hfamily :
        (E'.map (SmallEtale.inclusion B S hS)).map
          (Over.forget (B.obj S hS)) = Vfamily := by
      ext <;> rfl
    rw [hfamily]
    exact hV
  have hpresieveMap :
      (E'.presieve₀.map (SmallEtale.inclusion B S hS)).map
          (Over.forget (B.obj S hS)) =
        (E.presieve₀.map (SmallEtale.inclusion B S hS)).map
          (Over.forget (B.obj S hS)) := by
    apply presieve_map_injective_of_injective_obj
      (F := B.inclusion) (hobj := fun x y h => by
        cases x
        cases y
        cases h
        rfl)
    rw [← PreZeroHypercover.presieve₀_map, ← PreZeroHypercover.presieve₀_map,
      ← PreZeroHypercover.presieve₀_map, ← PreZeroHypercover.presieve₀_map,
      ← PreZeroHypercover.presieve₀_map, ← PreZeroHypercover.presieve₀_map]
    have hE'map : E'.map H₀ = Vfamily := by
      ext <;> rfl
    have hbase : (E'.map H₀).presieve₀ = (E.map H₀).presieve₀ := by
      rw [hE'map]
      exact (PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hcomb).symm
    simpa [H₀, Functor.comp_map, PreZeroHypercover.presieve₀_map,
      Presieve.map_ofArrows] using
      congrArg (fun R : Presieve (H₀.obj X) => R.map B.inclusion) hbase
  have hpresieve : E'.presieve₀ = E.presieve₀ :=
    smallEtale_presieve_map_injective (overForget_presieve_map_injective hpresieveMap)
  have hpre : E'.presieve₀ ∈ SmallEtale.precoverage B S hS X := by
    rw [SmallEtale.mem_precoverage_iff]
    exact ⟨E', rfl, hselected⟩
  have hgen : Sieve.generate E'.presieve₀ ∈
      SmallEtale.topology B S hS X :=
    Precoverage.generate_mem_toGrothendieck hpre
  rw [hpresieve] at hgen
  simpa [E, PreZeroHypercover.presieve₀] using hgen

private theorem section_eq_of_restrict_eq_on_cover
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    {U : SmallEtale B S hS} {I : Type (u + 1)}
    (V : I → SmallEtale B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : ∀ x : ((SmallEtale.toScheme B S hS).obj U),
      ∃ i y, ((SmallEtale.toScheme B S hS).map (g i)).base y = x)
    (hetale : ∀ i, Etale ((SmallEtale.toScheme B S hS).map (g i)))
    (s t : F.obj.obj (op U))
    (hrestr : ∀ i, F.obj.map (g i).op s = F.obj.map (g i).op t) : s = t := by
  let E := AddCommGrpCat.of (FreeAbelianGroup (ULift.{0, v} PUnit))
  let toSection (x : F.obj.obj (op U)) : E ⟶ F.obj.obj (op U) :=
    AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ : ULift.{0, v} PUnit => x)
  have hEq : toSection s = toSection t := by
    apply F.property.hom_ext_ofArrows g
      (smallEtale_cover_of_jointlySurjective_etale B S hS V g hcover hetale)
    intro i
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    simp [toSection, hrestr i]
  have hgen := congrArg (fun k : E ⟶ F.obj.obj (op U) =>
    k (FreeAbelianGroup.of (ULift.up PUnit.unit))) hEq
  change (FreeAbelianGroup.lift (fun _ : ULift.{0, v} PUnit => s)
      (FreeAbelianGroup.of (ULift.up PUnit.unit))) =
    (FreeAbelianGroup.lift (fun _ : ULift.{0, v} PUnit => t)
      (FreeAbelianGroup.of (ULift.up PUnit.unit))) at hgen
  simpa only [FreeAbelianGroup.lift_apply_of] using hgen

private theorem section_exists_of_compatible_cover
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    {U : SmallEtale B S hS} {I : Type (u + 1)}
    (V : I → SmallEtale B S hS) (g : ∀ i, V i ⟶ U)
    (hcover : Sieve.generate (Presieve.ofArrows V g) ∈
      SmallEtale.topology B S hS U)
    (s : ∀ i, F.obj.obj (op (V i)))
    (hcompat : ∀ {W : SmallEtale B S hS} (i j : I)
      (a : W ⟶ V i) (b : W ⟶ V j), a ≫ g i = b ≫ g j →
        F.obj.map a.op (s i) = F.obj.map b.op (s j)) :
    ∃ t : F.obj.obj (op U), ∀ i, F.obj.map (g i).op t = s i := by
  let E := AddCommGrpCat.of (FreeAbelianGroup (ULift.{0, v} PUnit))
  let toSection (x : F.obj.obj (op U)) : E ⟶ F.obj.obj (op U) :=
    AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ : ULift.{0, v} PUnit => x)
  let localHom (i : I) : E ⟶ F.obj.obj (op (V i)) :=
    AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ : ULift.{0, v} PUnit => s i)
  have hhomcompat : ∀ ⦃W : SmallEtale B S hS⦄ (i j : I)
      (a : W ⟶ V i) (b : W ⟶ V j), a ≫ g i = b ≫ g j →
        localHom i ≫ F.obj.map a.op = localHom j ≫ F.obj.map b.op := by
    intro W i j a b hab
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    simp [localHom, hcompat i j a b hab]
  obtain ⟨k, hk, -⟩ := F.property.existsUnique_amalgamation_ofArrows
    g hcover localHom hhomcompat
  refine ⟨k (FreeAbelianGroup.of (ULift.up PUnit.unit)), fun i => ?_⟩
  have hki := congrArg (fun m : E ⟶ F.obj.obj (op (V i)) =>
    m (FreeAbelianGroup.of (ULift.up PUnit.unit))) (hk i)
  change (F.obj.map (g i).op).hom
      (k.hom (FreeAbelianGroup.of (ULift.up PUnit.unit))) =
    (FreeAbelianGroup.lift (fun _ : ULift.{0, v} PUnit => s i))
      (FreeAbelianGroup.of (ULift.up PUnit.unit)) at hki
  rwa [FreeAbelianGroup.lift_apply_of] at hki

private theorem section_restrict_zero_of_disjoint_support
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})
    (U V : SmallEtale B S hS) (f : V ⟶ U) (s : F.obj.obj (op U))
    (hdisj : Disjoint (Set.range ((SmallEtale.toScheme B S hS).map f).base)
      (supportSection B S hS F U s)) :
    F.obj.map f.op s = 0 := by
  apply (map_eq_zero_iff_range_subset_zeroOpen B S hS F U s V f).2
  intro x hx
  have hnot : x ∉ supportSection B S hS F U s := by
    intro hs
    exact Set.disjoint_left.mp hdisj hx hs
  simpa [supportSection] using hnot

private theorem pullback_extra_branch_isClosed_in_source {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Etale f] [IsClosedImmersion g]
    (i : Z ⟶ X) (h : i ≫ f = g) [IsClosedImmersion i] :
    IsClosed (f.base ⁻¹' Set.range g.base \ Set.range i.base) := by
  simpa only [Scheme.Pullback.range_fst] using
    (pullback_extra_branch_isClosed f g i h)

private noncomputable def selectedBranchOpen {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (hf : Etale f) (g : Z ⟶ Y) [IsClosedImmersion g]
    (i : Z ⟶ X) (h : i ≫ f = g) [IsClosedImmersion i] : X.Opens := by
  let : Etale f := hf
  let E := f.base ⁻¹' Set.range g.base \ Set.range i.base
  exact ⟨Eᶜ, (pullback_extra_branch_isClosed_in_source f g i h).isOpen_compl⟩

private theorem selectedBranchOpen_inter_preimage {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (hf : Etale f) (g : Z ⟶ Y) [IsClosedImmersion g]
    (i : Z ⟶ X) (h : i ≫ f = g) [IsClosedImmersion i] :
    ((selectedBranchOpen f hf g i h : Set X) ∩
        (f.base ⁻¹' Set.range g.base)) =
      Set.range i.base := by
  classical
  have hsubset : Set.range i.base ⊆ f.base ⁻¹' Set.range g.base := by
    rintro x ⟨z, rfl⟩
    exact ⟨z, (congrArg (fun q : Z ⟶ Y => q.base z) h).symm⟩
  ext x
  constructor
  · rintro ⟨hxopen, hxpre⟩
    by_contra hxrange
    exact hxopen ⟨hxpre, hxrange⟩
  · exact fun hxrange => ⟨fun hxextra => hxextra.2 hxrange, hsubset hxrange⟩

private theorem pullback_point_in_diagonal_of_mem_closed_branch
    {X Y Z W : Scheme.{u}} (q : X ⟶ Y) (i : Z ⟶ X) (g : Z ⟶ Y)
    (hg : i ≫ q = g) [Mono g] (O : X.Opens)
    (hbranch : (O : Set X) ∩ q.base ⁻¹' Set.range g.base = Set.range i.base)
    (a b : W ⟶ X) (_ha : ∀ x, a.base x ∈ (O : Set X))
    (hb : ∀ x, b.base x ∈ (O : Set X)) (hab : a ≫ q = b ≫ q)
    (x : W) (hax : a.base x ∈ Set.range i.base) :
    (pullback.lift a b hab).base x ∈
      Set.range (pullback.diagonal q).base := by
  classical
  let k := pullback.lift a b hab
  obtain ⟨z, hz⟩ := hax
  have hqeq : q.base (a.base x) = q.base (b.base x) := by
    simpa only [← Scheme.Hom.comp_apply] using
      congrArg (fun f : W ⟶ Y => f.base x) hab
  have hqg : q.base (i.base z) = g.base z := by
    simpa only [← Scheme.Hom.comp_apply] using
      congrArg (fun f : Z ⟶ Y => f.base z) hg
  have hbin : b.base x ∈ q.base ⁻¹' Set.range g.base := by
    refine ⟨z, ?_⟩
    calc
      g.base z = q.base (i.base z) := hqg.symm
      _ = q.base (a.base x) := congrArg q.base hz
      _ = q.base (b.base x) := hqeq
  have hbi : b.base x ∈ Set.range i.base := by
    rw [← hbranch]
    exact ⟨hb x, hbin⟩
  let m := pullback.map g g q q i i (𝟙 Y)
    (by rw [Category.comp_id, hg]) (by rw [Category.comp_id, hg])
  have hfst : (pullback.fst q q).base (k.base x) ∈ Set.range i.base := by
    refine ⟨z, ?_⟩
    have hkfst : k ≫ pullback.fst q q = a := pullback.lift_fst a b hab
    simpa only [← Scheme.Hom.comp_apply, hkfst] using hz
  have hsnd : (pullback.snd q q).base (k.base x) ∈ Set.range i.base := by
    obtain ⟨z, hz⟩ := hbi
    refine ⟨z, ?_⟩
    have hksnd : k ≫ pullback.snd q q = b := pullback.lift_snd a b hab
    simpa only [← Scheme.Hom.comp_apply, hksnd] using hz
  have hkin : k.base x ∈ Set.range m.base := by
    rw [Scheme.Pullback.range_map]
    exact ⟨hfst, hsnd⟩
  have hmfst : m ≫ pullback.fst q q = pullback.fst g g ≫ i := by
    show pullback.lift (pullback.fst g g ≫ i) (pullback.snd g g ≫ i) _ ≫
      pullback.fst q q = pullback.fst g g ≫ i
    exact pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd q q = pullback.snd g g ≫ i := by
    show pullback.lift (pullback.fst g g ≫ i) (pullback.snd g g ≫ i) _ ≫
      pullback.snd q q = pullback.snd g g ≫ i
    exact pullback.lift_snd _ _ _
  have hfac : pullback.diagonal g ≫ m = i ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · show pullback.diagonal g ≫ (m ≫ pullback.fst q q) =
        i ≫ (pullback.diagonal q ≫ pullback.fst q q)
      rw [hmfst]
      simp [← Category.assoc]
    · show pullback.diagonal g ≫ (m ≫ pullback.snd q q) =
        i ≫ (pullback.diagonal q ≫ pullback.snd q q)
      rw [hmsnd]
      simp [← Category.assoc]
  have : IsIso (pullback.diagonal g) := by infer_instance
  have hm : m = (asIso (pullback.diagonal g)).inv ≫ i ≫ pullback.diagonal q := by
    calc
      m = (asIso (pullback.diagonal g)).inv ≫ pullback.diagonal g ≫ m := by simp
      _ = (asIso (pullback.diagonal g)).inv ≫ i ≫ pullback.diagonal q := by
        rw [hfac]
  have hmr : Set.range m.base ⊆ Set.range (pullback.diagonal q).base := by
    rw [hm]
    show Set.range ((pullback.diagonal q).base ∘
      ((asIso (pullback.diagonal g)).inv ≫ i).base) ⊆ _
    rw [Set.range_comp]
    exact Set.image_subset_iff.mpr (fun _ _ => Set.mem_range_self _)
  exact hmr hkin

/-- A morphism into `X ×_Y X` landing in the open diagonal equalizes the two projections. -/
private theorem comp_fst_eq_comp_snd_of_range_subset_diagonal {X Y W : Scheme.{u}} (q : X ⟶ Y)
    [IsOpenImmersion (pullback.diagonal q)] (k : W ⟶ pullback q q)
    (h : Set.range k.base ⊆ Set.range (pullback.diagonal q).base) :
    k ≫ pullback.fst q q = k ≫ pullback.snd q q := by
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ pullback.diagonal q = k := ⟨_, IsOpenImmersion.lift_fac _ _ h⟩
  simp

end AlgebraicGeometry.SmallEtale

end
