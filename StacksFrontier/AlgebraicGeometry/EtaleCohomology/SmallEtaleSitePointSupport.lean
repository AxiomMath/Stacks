module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# The support of a point of the small étale site

Let `B` be a big étale site containing a scheme `S` and let `p` be a point of the small étale
site of `S`, that is, a fibre functor `p.fiber` on that site in the sense of SGA 4 IV 6.3.
Restricting `p.fiber` along the inclusion of the open subschemes of `S` produces a functor on
`S.Opens` which behaves like the family of nonempty opens of a point: it is nonempty at `⊤`,
nonempty on intersections of opens where it is nonempty, and whenever it is nonempty on an open
it is nonempty on a member of any open cover of that open. Because the underlying space of a
scheme is sober, such a family is the family of opens containing a unique point of `S`, the
*support* of `p`.

The support controls which objects of the small étale site have nonempty fibre: the fibre of
`p` at an object `X` is nonempty exactly when the support lies in the open image of the étale
structure morphism of `X`.

## Main definitions

* `AlgebraicGeometry.siteOpen` and `AlgebraicGeometry.siteOpenι`: the object of the small
  étale site attached to an open subscheme of an object, and its structural monomorphism.
* `AlgebraicGeometry.openFiber`: the restriction of the fibre functor of a point to the
  open subschemes of `S`.
* `AlgebraicGeometry.siteEtaleImageOpen` and `AlgebraicGeometry.siteEtaleImageFactor`: the open
  image in `S` of an object of the small étale site, and the factorisation of the object
  through it.

## Main results

* `AlgebraicGeometry.exists_point_mem_iff_nonempty`: a functor on the opens of a scheme
  which is nonempty at `⊤`, stable under intersection and local on covers is the family of
  opens through a single point.
* `AlgebraicGeometry.sitePoint_has_supportPoint`: a point of the small étale site has a
  support point.
* `AlgebraicGeometry.sitePoint_cover_surjective`: a jointly surjective family of étale
  morphisms onto an object of the small étale site is jointly surjective on fibres.
* `AlgebraicGeometry.exists_isAffine_refinement_fiber`: every element of the fibre of a point
  is the image of an element over an affine object.
* `AlgebraicGeometry.sitePoint_clopen_lift`: an element of a fibre lifts either to a clopen
  subobject or to its complement.
* `AlgebraicGeometry.sitePoint_fiber_nonempty_implies_support_in_image` and
  `AlgebraicGeometry.sitePoint_fiber_nonempty_of_support_in_image`: the fibre at `X` is
  nonempty precisely when the support lies in the image of `X`.
* `AlgebraicGeometry.sitePoint_fiber_isEmpty_of_no_point_over_support`: the fibre at `X` is
  empty when no point of `X` lies over the support.

## References

* [Stacks Project, Tag 04HU](https://stacks.math.columbia.edu/tag/04HU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Jointly surjective families of étale morphisms -/

/-- Every element of the fibre of a point at `X` comes from an element over a member of any
covering family of `X`. -/
private theorem exists_fiber_preimage_of_presieve₀_mem
    (p : (SmallEtale.topology B S hS).Point.{max u w}) {X : SmallEtale B S hS}
    (H : PreZeroHypercover.{u + 1} X) (hH : H.presieve₀ ∈ SmallEtale.precoverage B S hS X)
    (a : p.fiber.obj X) : ∃ j, ∃ b : p.fiber.obj (H.X j), p.fiber.map (H.f j) b = a := by
  obtain ⟨T, g, hg, b, hb⟩ := p.jointly_surjective _
    (Precoverage.generate_mem_toGrothendieck hH) a
  obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff (Y := H.X) (f := H.f) g).1 hg
  exact ⟨j, p.fiber.map k b, by rw [← Functor.map_comp_apply, ← hk]; exact hb⟩

/-- A family of étale morphisms onto an object `X` of the small étale site whose images cover
the underlying space of `X` is jointly surjective on the fibres of a point of the site: every
element of `p.fiber.obj X` comes from an element over one of the members. -/
public theorem sitePoint_cover_surjective
    (p : (SmallEtale.topology B S hS).Point.{max u w})
    {X : SmallEtale B S hS} {I : Type u}
    (Y : I → SmallEtale B S hS) (f : ∀ i, Y i ⟶ X)
    (hc : ∀ x : (SmallEtale.toScheme B S hS).obj X,
      ∃ i, x ∈ Set.range ((SmallEtale.toScheme B S hS).map (f i)))
    (he : ∀ i, Etale ((SmallEtale.toScheme B S hS).map (f i)))
    (a : p.fiber.obj X) : ∃ i b, p.fiber.map (f i) b = a := by
  let E : PreZeroHypercover.{u + 1} X.obj.left :=
    { I₀ := ULift.{u + 1} I
      X i := (Y i.down).obj.left
      f i := (f i.down).hom.left }
  have hE : IsEtaleCovering ⟨X.obj.left, E⟩ := by
    show (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map, Presieve.map_ofArrows]
    exact (Scheme.ofArrows_mem_precoverage_iff (@Etale)).2
      ⟨fun x => (hc x).elim fun i hi => ⟨ULift.up i, hi⟩, fun i => he i.down⟩
  obtain ⟨⟨Z, E'⟩, hE', hZ, hcomb⟩ := B.exists_covering_rep ⟨X.obj.left, E⟩ hE
  change X.obj.left = Z at hZ
  subst Z
  obtain ⟨α, hY, hf⟩ := hcomb.2
  let Y' (j : E'.I₀) : SmallEtale B S hS :=
    ⟨Over.mk (E'.f j ≫ X.obj.hom), by
      show Etale (B.inclusion.map (E'.f j ≫ X.obj.hom))
      rw [hf j, Category.assoc, Over.w, Functor.map_comp]
      infer_instance⟩
  let f' (j : E'.I₀) : Y' j ⟶ X := ObjectProperty.homMk (Over.homMk (E'.f j))
  let H : PreZeroHypercover.{u + 1} X := { I₀ := E'.I₀, X := Y', f := f' }
  have hH : H.presieve₀ ∈ SmallEtale.precoverage B S hS X := ⟨H, rfl, hE'⟩
  obtain ⟨j, b, hb⟩ := exists_fiber_preimage_of_presieve₀_mem B S hS p H hH a
  let l : Y' j ⟶ Y (α j).down := ObjectProperty.homMk
    (Over.homMk (eqToHom (hY j)) (by
      show eqToHom (hY j) ≫ (Y (α j).down).obj.hom = E'.f j ≫ X.obj.hom
      rw [hf j, Category.assoc, Over.w]))
  refine ⟨(α j).down, p.fiber.map l b, ?_⟩
  have hl : l ≫ f (α j).down = f' j :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (hf j).symm)
  rw [← Functor.map_comp_apply, hl]
  exact hb

/-! ### Open subobjects of an object of the small étale site -/

/-- The object of the small étale site of `S` attached to an open subscheme of an object `X`. -/
public def siteOpen (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens) : SmallEtale B S hS :=
  ⟨Over.mk (ObjectProperty.homMk (U.ι ≫ B.inclusion.map X.obj.hom) :
    B.obj U.toScheme (Scheme.size_lt_of_isOpenImmersion U.ι X.obj.left.property) ⟶
      B.obj S hS),
    inferInstanceAs (Etale (U.ι ≫ B.inclusion.map X.obj.hom))⟩

/-- The structural morphism from the object attached to an open subscheme of `X` to `X`. -/
public def siteOpenι (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens) : siteOpen B S hS X U ⟶ X :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk U.ι))

/-- Every element of the fibre of a point of the small étale site is the image of an element
over an object with affine underlying scheme. -/
public theorem exists_isAffine_refinement_fiber
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (a : p.fiber.Elements) :
    ∃ b : p.fiber.Elements, IsAffine ((SmallEtale.toScheme B S hS).obj b.obj) ∧
      Nonempty (b ⟶ a) := by
  let X := (SmallEtale.toScheme B S hS).obj a.obj
  let Y (U : X.affineOpens) := siteOpen B S hS a.obj U.1
  let f (U : X.affineOpens) := siteOpenι B S hS a.obj U.1
  obtain ⟨U, b, hb⟩ := sitePoint_cover_surjective B S hS p Y f (fun x => by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (x := x) (U := ⊤) (by trivial)
    exact ⟨⟨U, hU⟩, ⟨⟨x, hxU⟩, rfl⟩⟩) (fun U => inferInstanceAs (Etale U.1.ι)) a.val
  exact ⟨p.fiber.elementsMk (Y U) b, U.2, ⟨Functor.Elements.homMk (f U) hb⟩⟩

/-- The open complement of an open subset which is also closed. -/
public abbrev opensCompl {T : Scheme.{u}} (U : T.Opens)
    (hc : IsClosed (U : Set T)) : T.Opens := ⟨(U : Set T)ᶜ, hc.isOpen_compl⟩

/-- An element of the fibre of a point of the small étale site at `X` lifts either to the
object attached to a clopen subset `U` of `X` or to the object attached to its complement. -/
public theorem sitePoint_clopen_lift
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (X : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj X).Opens)
    (hc : IsClosed (U : Set ((SmallEtale.toScheme B S hS).obj X))) (a : p.fiber.obj X) :
    (∃ b, p.fiber.map (siteOpenι B S hS X U) b = a) ∨
      ∃ b : p.fiber.obj (siteOpen B S hS X (opensCompl U hc)),
        p.fiber.map (siteOpenι B S hS X (opensCompl U hc)) b = a := by
  classical
  let V : ULift.{u} Bool → ((SmallEtale.toScheme B S hS).obj X).Opens :=
    fun i => if i.down then U else opensCompl U hc
  obtain ⟨⟨_ | _⟩, b, hb⟩ := sitePoint_cover_surjective B S hS p
    (fun i => siteOpen B S hS X (V i)) (fun i => siteOpenι B S hS X (V i))
    (fun x => by
      by_cases hx : x ∈ U
      · exact ⟨ULift.up true, ⟨⟨x, hx⟩, rfl⟩⟩
      · exact ⟨ULift.up false, ⟨⟨x, hx⟩, rfl⟩⟩)
    (fun i => inferInstanceAs (Etale (V i).ι)) a
  exacts [Or.inr ⟨b, hb⟩, Or.inl ⟨b, hb⟩]

/-! ### The support point -/

/-- A functor on the opens of a scheme which is nonempty at `⊤`, nonempty on the intersection
of two opens where it is nonempty, and nonempty on a member of every open cover of an open
where it is nonempty, is the family of opens containing a single point. -/
public theorem exists_point_mem_iff_nonempty (F : S.Opens ⥤ Type w)
    (hTop : Nonempty (F.obj ⊤))
    (hInter : ∀ U V, Nonempty (F.obj U) → Nonempty (F.obj V) → Nonempty (F.obj (U ⊓ V)))
    (hCover : ∀ (U : S.Opens) (I : Type u) (V : I → S.Opens), (∀ i, V i ≤ U) →
      (⋃ i, (V i : Set S)) = (U : Set S) → Nonempty (F.obj U) → ∃ i, Nonempty (F.obj (V i))) :
    ∃ x : S, ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty (F.obj U) := by
  classical
  let M : Type u := {U : S.Opens // ¬ Nonempty (F.obj U)}
  let bad : Set S := ⋃ i : M, (i.1 : Set S)
  let Z : Set S := badᶜ
  have hbad : IsOpen bad := isOpen_iUnion fun i => i.1.2
  have hZclosed : IsClosed Z := isClosed_compl_iff.mpr hbad
  have hZne : Z.Nonempty := by
    by_contra hn
    have hcov : bad = Set.univ := Set.compl_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨i, hi⟩ := hCover ⊤ M (fun i => i.1) (fun _ => le_top)
      (hcov.trans TopologicalSpace.Opens.coe_top.symm) hTop
    exact i.2 hi
  have hPZ (U : S.Opens) : Nonempty (F.obj U) ↔ ∃ x, x ∈ Z ∧ x ∈ (U : Set S) := by
    constructor
    · intro hFU
      by_contra hdisj
      have hUbad : (U : Set S) ⊆ bad := fun x hxU => not_not.mp fun hx => hdisj ⟨x, hx, hxU⟩
      let V : M → S.Opens := fun i => U ⊓ i.1
      have hVcover : (⋃ i, (V i : Set S)) = (U : Set S) := Set.ext fun x =>
        ⟨fun hx => (Set.mem_iUnion.mp hx).elim fun _ hxi => hxi.1,
          fun hxU => (Set.mem_iUnion.mp (hUbad hxU)).elim fun i hxi =>
            Set.mem_iUnion.mpr ⟨i, hxU, hxi⟩⟩
      obtain ⟨i, hi⟩ := hCover U M V (fun _ => inf_le_left) hVcover hFU
      exact i.2 (hi.map (F.map (homOfLE (inf_le_right : V i ≤ i.1))))
    · rintro ⟨x, hxZ, hxU⟩
      by_contra hFU
      exact hxZ (Set.mem_iUnion.mpr ⟨⟨U, hFU⟩, hxU⟩)
  have hpre : IsPreirreducible Z := by
    intro A D hA hD hAZ hDZ
    have hFU : Nonempty (F.obj ⟨A, hA⟩) := (hPZ ⟨A, hA⟩).2 hAZ
    have hFV : Nonempty (F.obj ⟨D, hD⟩) := (hPZ ⟨D, hD⟩).2 hDZ
    obtain ⟨x, hxZ, hxUV⟩ := (hPZ (⟨A, hA⟩ ⊓ ⟨D, hD⟩)).1 (hInter _ _ hFU hFV)
    exact ⟨x, hxZ, hxUV.1, hxUV.2⟩
  obtain ⟨x, hx⟩ := QuasiSober.sober ⟨hZne, hpre⟩ hZclosed
  exact ⟨x, fun U => (hx.mem_open_set_iff U.2).trans (hPZ U).symm⟩

/-- The morphism from the object of the small étale site attached to an open subscheme of `S`
to the final object `S / S`. -/
public def openToSmallEtaleFinal (U : S.Opens) :
    (opensToBoundedEtale B S hS).obj U ⟶ SmallEtale.final B S hS :=
  ObjectProperty.homMk (Over.homMk ((opensToBoundedEtale B S hS).obj U).obj.hom)

/-- The restriction of the fibre functor of a point of the small étale site to the open
subschemes of `S`. -/
public def openFiber (p : (SmallEtale.topology B S hS).Point.{max u w}) :
    S.Opens ⥤ Type (max u w) := opensToBoundedEtale B S hS ⋙ p.fiber

/-- The open fibre functor is nonempty at `⊤`. -/
public theorem openFiber_top_nonempty (p : (SmallEtale.topology B S hS).Point.{max u w}) :
    Nonempty ((openFiber B S hS p).obj ⊤) := by
  let U : S.Opens := ⊤
  let f := openToSmallEtaleFinal B S hS U
  have : IsIso (B.inclusion.map ((opensToBoundedEtale B S hS).obj U).obj.hom) :=
    (Scheme.topIso S).isIso_hom
  have hObj : IsIso ((opensToBoundedEtale B S hS).obj U).obj.hom :=
    isIso_of_reflects_iso _ B.inclusion
  have : IsIso ((SmallEtale.inclusion B S hS).map f) := by
    let G := Over.forget (B.obj S hS)
    have : IsIso (G.map ((SmallEtale.inclusion B S hS).map f)) := hObj
    exact isIso_of_reflects_iso _ G
  have : IsIso f := isIso_of_reflects_iso _ (SmallEtale.inclusion B S hS)
  have hU : IsTerminal ((opensToBoundedEtale B S hS).obj U) :=
    IsTerminal.ofIso (SmallEtale.finalIsTerminal B S hS) (asIso f).symm
  exact ⟨(p.uniqueFiberObj _ hU).default⟩

/-- The open fibre functor is nonempty on the intersection of two opens where it is nonempty. -/
public theorem openFiber_inter_nonempty (p : (SmallEtale.topology B S hS).Point.{max u w})
    (U V : S.Opens) (hU : Nonempty ((openFiber B S hS p).obj U))
    (hV : Nonempty ((openFiber B S hS p).obj V)) :
    Nonempty ((openFiber B S hS p).obj (U ⊓ V)) := by
  classical
  let F := p.fiber
  let X := (opensToBoundedEtale B S hS).obj U
  let Y := (opensToBoundedEtale B S hS).obj V
  let x : F.obj X := Classical.choice hU
  let y : F.obj Y := Classical.choice hV
  let a : F.Elements := F.elementsMk X x
  let b : F.Elements := F.elementsMk Y y
  let z := IsCofiltered.min a b
  let fU : z ⟶ a := IsCofiltered.minToLeft a b
  let fV : z ⟶ b := IsCofiltered.minToRight a b
  let W : S.Opens := U ⊓ V
  let ZS : Scheme := (SmallEtale.toScheme B S hS).obj z.obj
  let gU : ZS ⟶ U.toScheme := (SmallEtale.toScheme B S hS).map fU.hom
  let gV : ZS ⟶ V.toScheme := (SmallEtale.toScheme B S hS).map fV.hom
  have hbase : gU ≫ U.ι = gV ≫ V.ι := by
    have h₁ := congrArg (fun f => B.inclusion.map f)
      (Over.w ((SmallEtale.inclusion B S hS).map fU.hom))
    have h₂ := congrArg (fun f => B.inclusion.map f)
      (Over.w ((SmallEtale.inclusion B S hS).map fV.hom))
    change gU ≫ U.ι = _ at h₁
    change gV ≫ V.ι = _ at h₂
    exact h₁.trans h₂.symm
  let g : ZS ⟶ W.toScheme := (isPullback_opens_inf U V).lift gU gV hbase
  have hgU : g ≫ S.homOfLE inf_le_left = gU := (isPullback_opens_inf U V).lift_fst _ _ _
  let g' : B.inclusion.obj z.obj.obj.left ⟶
      B.inclusion.obj ((opensToBoundedEtale B S hS).obj W).obj.left := by
    simpa [ZS, opensToBoundedEtale, SmallEtale.toScheme, BigEtaleOver.toScheme,
      BigEtaleOver.forget, BigEtaleSite.inclusion, schemeBelowInclusion,
      schemeSizeBelow] using g
  let k : z.obj ⟶ (opensToBoundedEtale B S hS).obj W := by
    apply ObjectProperty.homMk
    refine Over.homMk (B.inclusion.preimage
      (X := z.obj.obj.left)
      (Y := ((opensToBoundedEtale B S hS).obj W).obj.left) g') ?_
    apply B.inclusion.map_injective
    show B.inclusion.map (B.inclusion.preimage g') ≫ _ = _
    rw [B.inclusion.map_preimage]
    have hg' : g' = g := by
      simp [g', ZS, opensToBoundedEtale, BigEtaleSite.inclusion, schemeBelowInclusion]
    rw [hg']
    show g ≫ W.ι = B.inclusion.map z.obj.obj.hom
    calc
      g ≫ W.ι = (g ≫ S.homOfLE inf_le_left) ≫ U.ι := by
        simp [Category.assoc, Scheme.homOfLE_ι]
      _ = gU ≫ U.ι := by rw [hgU]
      _ = B.inclusion.map z.obj.obj.hom :=
        congrArg (fun f => B.inclusion.map f) (Over.w ((SmallEtale.inclusion B S hS).map fU.hom))
  exact ⟨F.map k z.val⟩

/-- The open fibre functor is local on open covers: if it is nonempty on an open `U` covered by
opens `V i`, it is nonempty on some `V i`. -/
public theorem openFiber_cover (p : (SmallEtale.topology B S hS).Point.{max u w})
    (U : S.Opens) (I : Type u) (V : I → S.Opens) (hle : ∀ i, V i ≤ U)
    (hcover : (⋃ i, (V i : Set S)) = (U : Set S))
    (hU : Nonempty ((openFiber B S hS p).obj U)) :
    ∃ i, Nonempty ((openFiber B S hS p).obj (V i)) := by
  classical
  let XU := (opensToBoundedEtale B S hS).obj U
  let hUsize : B.Contains U.toScheme := Scheme.size_lt_of_isOpenImmersion U.ι hS
  let E : PreZeroHypercover.{u + 1} (B.obj U.toScheme hUsize) :=
    { I₀ := ULift.{u + 1, u} I
      X i := B.obj (V i.down).toScheme (Scheme.size_lt_of_isOpenImmersion (V i.down).ι hS)
      f i := B.inclusion.preimage (S.homOfLE (hle i.down)) }
  have hEtale : IsEtaleCovering ⟨B.obj U.toScheme hUsize, E⟩ := by
    show (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map, Presieve.map_ofArrows]
    apply (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2
    constructor
    · intro x
      have hx : (x.1 : S) ∈ (U : Set S) := x.2
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (by rw [hcover]; exact hx)
      refine ⟨ULift.up i, ⟨⟨x.1, hxi⟩, ?_⟩⟩
      rw [B.inclusion.map_preimage]
      exact Subtype.ext (Scheme.homOfLE_apply (hle i) ⟨x.1, hxi⟩)
    · intro i
      rw [B.inclusion.map_preimage]
      infer_instance
  obtain ⟨⟨Trep, ErepFam⟩, hErep, hTarget, hcomb⟩ :=
    B.exists_covering_rep ⟨B.obj U.toScheme hUsize, E⟩ hEtale
  change B.obj U.toScheme hUsize = Trep at hTarget
  subst Trep
  let uS : B.obj U.toScheme hUsize ⟶ B.obj S hS := ObjectProperty.homMk U.ι
  let Yrep : ErepFam.I₀ → SmallEtale B S hS := fun j =>
    ⟨Over.mk (ErepFam.f j ≫ uS), by
      show Etale (B.inclusion.map (ErepFam.f j ≫ uS))
      rw [Functor.map_comp]
      show Etale (B.inclusion.map (ErepFam.f j) ≫ U.ι)
      have hm := BigEtaleSite.IsCovering.etale hErep
      change (ErepFam.map B.inclusion).presieve₀ ∈ _ at hm
      have hi := (Scheme.ofArrows_mem_precoverage_iff
        (P := @Etale) (f := fun k => B.inclusion.map (ErepFam.f k))).1 hm
      have : Etale (B.inclusion.map (ErepFam.f j)) := hi.2 j
      infer_instance⟩
  let Esmall : PreZeroHypercover.{u + 1} XU :=
    { I₀ := ErepFam.I₀
      X := Yrep
      f j := ObjectProperty.homMk (Over.homMk (ErepFam.f j)) }
  have hCov : Esmall.presieve₀ ∈ (SmallEtale.precoverage B S hS).coverings XU :=
    ⟨Esmall, rfl, hErep⟩
  obtain ⟨j, z, -⟩ := exists_fiber_preimage_of_presieve₀_mem B S hS p Esmall hCov
    (Classical.choice hU)
  obtain ⟨α, hXs, hfs⟩ := hcomb.2
  let i := (α j).down
  have hα : α j = ULift.up i := by simpa [i] using (ULift.up_down (α j)).symm
  let XVi := (opensToBoundedEtale B S hS).obj (V i)
  have hXV : ErepFam.X j = E.X (ULift.up i) := by
    simpa only [hα, ULift.down_up] using hXs j
  have hXarrow : ErepFam.f j = eqToHom hXV ≫ E.f (ULift.up i) := by
    simpa only [hXV, hα, ULift.down_up] using hfs j
  have hViSize : B.Contains (V i).toScheme := Scheme.size_lt_of_isOpenImmersion (V i).ι hS
  have hEMap : B.inclusion.map (E.f (ULift.up i)) = S.homOfLE (hle i) := by
    show B.inclusion.map (B.inclusion.preimage
      (X := B.obj (V i).toScheme hViSize) (Y := B.obj U.toScheme hUsize)
      (S.homOfLE (hle i))) = _
    exact B.inclusion.map_preimage _
  have hOverOpen : E.f (ULift.up i) ≫ XU.obj.hom = XVi.obj.hom := by
    dsimp only [XU, XVi, opensToBoundedEtale]
    apply B.inclusion.map_injective
    rw [Functor.map_comp, hEMap]
    show S.homOfLE (hle i) ≫ U.ι = (V i).ι
    exact Scheme.homOfLE_ι S (hle i)
  let jOpen : Esmall.X j ⟶ XVi := by
    apply ObjectProperty.homMk
    refine Over.homMk (eqToHom hXV) ?_
    calc
      eqToHom hXV ≫ XVi.obj.hom =
          eqToHom hXV ≫ (E.f (ULift.up i) ≫ XU.obj.hom) := by rw [hOverOpen]
      _ = (eqToHom hXV ≫ E.f (ULift.up i)) ≫ XU.obj.hom := (Category.assoc _ _ _).symm
      _ = ErepFam.f j ≫ XU.obj.hom := by rw [← hXarrow]
  exact ⟨i, ⟨p.fiber.map jOpen z⟩⟩

/-- **The support of a point of the small étale site.** There is a unique point of `S` whose
open neighbourhoods are exactly the opens on which the fibre functor of `p` is nonempty. -/
public theorem sitePoint_has_supportPoint (p : (SmallEtale.topology B S hS).Point.{max u w}) :
    ∃ x : S, ∀ U : S.Opens,
      (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U) :=
  exists_point_mem_iff_nonempty S (openFiber B S hS p)
    (openFiber_top_nonempty B S hS p)
    (fun U V hU hV => openFiber_inter_nonempty B S hS p U V hU hV)
    (fun U I V hle hcover hU => openFiber_cover B S hS p U I V hle hcover hU)

/-! ### The open image of an object of the small étale site -/

/-- The image in `S` of an object of the small étale site, as an open subscheme. -/
public def siteEtaleImageOpen (X : SmallEtale B S hS) : S.Opens :=
  ⟨Set.range (B.inclusion.map X.obj.hom), (B.inclusion.map X.obj.hom).isOpenMap.isOpen_range⟩

/-- The factorisation of an object of the small étale site through its open image. -/
public def siteEtaleImageFactor (X : SmallEtale B S hS) :
    X ⟶ (opensToBoundedEtale B S hS).obj (siteEtaleImageOpen B S hS X) := by
  let O := siteEtaleImageOpen B S hS X
  let f := B.inclusion.map X.obj.hom
  let hOSize : B.Contains O.toScheme := Scheme.size_lt_of_isOpenImmersion O.ι hS
  have hfRange : Set.range f ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨f z, ⟨z, rfl⟩⟩, rfl⟩
  let hfactor : B.inclusion.obj X.obj.left ⟶ B.inclusion.obj (B.obj O.toScheme hOSize) :=
    IsOpenImmersion.lift O.ι f hfRange
  apply ObjectProperty.homMk
  refine Over.homMk (B.inclusion.preimage hfactor) ?_
  apply B.inclusion.map_injective
  change B.inclusion.map (B.inclusion.preimage hfactor) ≫ _ = _
  rw [B.inclusion.map_preimage]
  exact IsOpenImmersion.lift_fac O.ι f hfRange

/-- The factorisation through the open image is, on underlying schemes, the canonical lift of
the étale structure morphism along the open immersion of its image. -/
public theorem siteEtaleImageFactor_map (X : SmallEtale B S hS) :
    B.inclusion.map (siteEtaleImageFactor B S hS X).hom.left =
      IsOpenImmersion.lift (siteEtaleImageOpen B S hS X).ι (B.inclusion.map X.obj.hom) (by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨(B.inclusion.map X.obj.hom) z, ⟨z, rfl⟩⟩, rfl⟩) := by
  dsimp [siteEtaleImageFactor]
  show B.inclusion.map (B.inclusion.preimage _) = _
  exact B.inclusion.map_preimage _

/-- If the fibre of a point at `X` is nonempty then the support of the point lies in the open
image of `X`. -/
public theorem sitePoint_fiber_nonempty_implies_support_in_image
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (X : SmallEtale B S hS) (ha : Nonempty (p.fiber.obj X)) :
    x ∈ (siteEtaleImageOpen B S hS X : Set S) :=
  (hx (siteEtaleImageOpen B S hS X)).2 (ha.map (p.fiber.map (siteEtaleImageFactor B S hS X)))

/-- If the support of a point lies in the open image of `X` then the fibre at `X` is
nonempty. -/
public theorem sitePoint_fiber_nonempty_of_support_in_image
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (X : SmallEtale B S hS) (hxX : x ∈ (siteEtaleImageOpen B S hS X : Set S)) :
    Nonempty (p.fiber.obj X) := by
  classical
  let O := siteEtaleImageOpen B S hS X
  let T := (opensToBoundedEtale B S hS).obj O
  let E : PreZeroHypercover T := { I₀ := PUnit, X _ := X, f _ := siteEtaleImageFactor B S hS X }
  let f := B.inclusion.map X.obj.hom
  have hfRange : Set.range f ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨f z, ⟨z, rfl⟩⟩, rfl⟩
  have hSingletonBound : Cardinal.mk PUnit ≤ B.coveringBound :=
    (B.coverings_isSite.1 (𝟙 (B.obj O.toScheme (Scheme.size_lt_of_isOpenImmersion O.ι hS)))).2
  have hcover : SmallEtale.IsCovering B S hS ⟨T, E⟩ := by
    show B.IsCovering ⟨B.obj O.toScheme (Scheme.size_lt_of_isOpenImmersion O.ι hS),
      (E.map (SmallEtale.inclusion B S hS)).map (Over.forget (B.obj S hS))⟩
    show CovBounded IsEtaleCovering B.coveringBound _
    refine ⟨?_, hSingletonBound⟩
    show (((E.map (SmallEtale.inclusion B S hS)).map
      (Over.forget (B.obj S hS))).map B.inclusion).presieve₀ ∈
        Scheme.etalePrecoverage (B.inclusion.obj (B.obj O.toScheme
          (Scheme.size_lt_of_isOpenImmersion O.ι hS)))
    rw [PreZeroHypercover.presieve₀_map, Presieve.map_ofArrows]
    apply (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2
    constructor
    · intro y
      show ∃ i, y ∈ Set.range (B.inclusion.map ((E.f i).hom).left)
      have hmap : B.inclusion.map (E.f PUnit.unit).hom.left =
          IsOpenImmersion.lift O.ι f hfRange := by
        show B.inclusion.map (siteEtaleImageFactor B S hS X).hom.left = _
        simpa [O, f] using siteEtaleImageFactor_map B S hS X
      obtain ⟨z, hz⟩ := (show (y.1 : S) ∈ Set.range f from y.2)
      refine ⟨PUnit.unit, ⟨z, ?_⟩⟩
      rw [hmap]
      apply Subtype.ext
      calc
        O.ι ((IsOpenImmersion.lift O.ι f hfRange) z) = f z :=
          congrArg (fun k => k z) (IsOpenImmersion.lift_fac O.ι f hfRange)
        _ = y.1 := hz
    · intro i
      show Etale (B.inclusion.map (E.f i).hom.left)
      have : Etale (IsOpenImmersion.lift O.ι f hfRange ≫ O.ι) := by
        rw [IsOpenImmersion.lift_fac]
        exact X.property
      have : Etale (IsOpenImmersion.lift O.ι f hfRange) := Etale.of_comp _ O.ι
      rwa [siteEtaleImageFactor_map]
  obtain ⟨_, y, -⟩ := exists_fiber_preimage_of_presieve₀_mem B S hS p E ⟨E, rfl, hcover⟩
    (Classical.choice ((hx O).mp hxX))
  exact ⟨y⟩

/-- The fibre of a point of the small étale site at `X` is empty when no point of `X` lies over
the support of the point. -/
public theorem sitePoint_fiber_isEmpty_of_no_point_over_support
    (p : (SmallEtale.topology B S hS).Point.{max u w}) (x : S)
    (hx : ∀ U : S.Opens, (x ∈ (U : Set S)) ↔ Nonempty ((openFiber B S hS p).obj U))
    (X : SmallEtale B S hS)
    (hno : ∀ y : (SmallEtale.toScheme B S hS).obj X, (B.inclusion.map X.obj.hom) y ≠ x) :
    IsEmpty (p.fiber.obj X) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨y, hy⟩ := sitePoint_fiber_nonempty_implies_support_in_image B S hS p x hx X ⟨a⟩
  exact hno y hy

end AlgebraicGeometry

end
