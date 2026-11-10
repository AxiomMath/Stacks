module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariski.CompatibleData

/-!
# Restricting a big Zariski sheaf to the small sites

For a sheaf `F` on the big Zariski site of `S` and a scheme `T` over `S`, restriction along
the small-to-big functor of Tag 020Y, followed by the identification of the small Zariski
site of `T` with the opens of its space (Tag 020X), produces a sheaf on the space of `T`.
This file constructs that sheaf, computes its sections, and builds the comparison maps it
carries along a morphism of schemes over `S`.

## Main definitions

* `AlgebraicGeometry.canonicalSmallSheaf` and `AlgebraicGeometry.canonicalSmallSheafFunctor`
  — the sheaf on the space of `T`, and its functoriality in `F`.
* `AlgebraicGeometry.smallOpenObject` and `AlgebraicGeometry.smallSiteArrow` — the chosen
  small-site representative of an open subset, and the arrow between two representatives
  induced by a morphism of schemes over `S`.
* `AlgebraicGeometry.canonicalSmallPairMap` and
  `AlgebraicGeometry.canonicalSmallPullbackFamily` — the section maps along a morphism over
  the base, and the compatible family they form.

## Main results

* `AlgebraicGeometry.canonicalSmallTopSectionsIso` — global sections of the restricted sheaf
  at `T` are the sections of `F` at `T`.
* `AlgebraicGeometry.canonicalSmallSiteIso` — on the small Zariski site the restricted sheaf
  is the composition of `F` with the small-to-big functor.
* `AlgebraicGeometry.canonicalSmallPullbackFamily_comp` — the section maps compose.
* `AlgebraicGeometry.smallSiteArrow_isIso` — along an open immersion the arrows between
  small-site representatives are isomorphisms.

## References

* [Stacks Project, Tag 0213](https://stacks.math.columbia.edu/tag/0213)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The representative in the small Zariski site of an open of the underlying space. -/
public noncomputable def smallOpenObject
    (T : BigZariskiOver B S hS)
    (U : T.left.1.Opens) : SmallZariski B T.left.1 T.left.2 := by
  let U₀ : B.Schemes :=
    ⟨(U : Scheme), (Scheme.size_coe_opens_le T.left.1 U).trans_lt T.left.2⟩
  let i : U₀ ⟶ T.left := ObjectProperty.homMk U.ι
  refine ⟨Over.mk i, ?_⟩
  change IsOpenImmersion (B.inclusion.map i)
  simpa [i] using (inferInstance : IsOpenImmersion U.ι)

/-- Its image under the comparison with opens is the given open. -/
public theorem smallOpenObject_toOpens
    (T : BigZariskiOver B S hS)
    (U : T.left.1.Opens) :
    (smallZariskiToOpens B T.left.1 T.left.2).obj
      (smallOpenObject B S hS T U) = U := by
  simp [smallZariskiToOpens, smallOpenObject]

/-- The image of a small-site representative lies in the image of any representative of a
larger open. -/
public theorem smallSiteArrow_range_subset
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    Set.range (B.inclusion.map X.obj.hom ≫ (BigZariskiOver.toScheme B S hS).map f) ⊆
      Set.range (B.inclusion.map Y.obj.hom) := by
  let i := B.inclusion.map X.obj.hom
  let j := B.inclusion.map Y.obj.hom
  let g := (BigZariskiOver.toScheme B S hS).map f
  rintro _ ⟨x, rfl⟩
  have hxU : i x ∈ (smallZariskiToOpens B T'.left.1 T'.left.2).obj X :=
    ⟨x, rfl⟩
  have hxV := hXY hxU
  change i x ∈ ((Opens.map g.base).obj
    ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)).1 at hxV
  change g.base.hom' (i.base.hom' x) ∈
    ((smallZariskiToOpens B T.left.1 T.left.2).obj Y).1 at hxV
  have hxV' : g.base.hom' (i.base.hom' x) ∈ j.opensRange := by
    simpa [j, smallZariskiToOpens,
      smallZariskiOpenImmersion] using hxV
  obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hxV'
  exact ⟨y, hy⟩

/-- A map between arbitrary open-site representatives over a scheme. -/
public noncomputable def smallSiteArrow
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    (smallZariskiToBigZariskiFunctor B T'.left ⟨S, hS⟩ T'.hom).obj X ⟶
      (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj Y := by
  let i := B.inclusion.map X.obj.hom
  let j := B.inclusion.map Y.obj.hom
  let g := (BigZariskiOver.toScheme B S hS).map f
  have hset : Set.range (i ≫ g) ⊆ Set.range j := smallSiteArrow_range_subset B S hS f X Y hXY
  let ℓ := IsOpenImmersion.lift j (i ≫ g) hset
  let ℓ' := B.inclusion.preimage ℓ
  have hℓ : B.inclusion.map ℓ' = ℓ := B.inclusion.map_preimage ℓ
  let A := (smallZariskiToBigZariskiFunctor B T'.left
    ⟨S, hS⟩ T'.hom).obj X
  let C := (smallZariskiToBigZariskiFunctor B T.left
    ⟨S, hS⟩ T.hom).obj Y
  refine Over.homMk (U := A) (V := C) ℓ' ?_
  apply B.inclusion.map_injective
  rw [B.inclusion.map_comp, hℓ]
  change ℓ ≫ j ≫ B.inclusion.map T.hom = i ≫ B.inclusion.map T'.hom
  calc
    ℓ ≫ j ≫ B.inclusion.map T.hom = (ℓ ≫ j) ≫ B.inclusion.map T.hom := by
      simp [Category.assoc]
    _ = (i ≫ B.inclusion.map f.left) ≫ B.inclusion.map T.hom := by
      rw [show ℓ ≫ j = i ≫ B.inclusion.map f.left from IsOpenImmersion.lift_fac j (i ≫ g) hset]
    _ = i ≫ B.inclusion.map (f.left ≫ T.hom) := by
      rw [B.inclusion.map_comp]
      simp [Category.assoc]
    _ = i ≫ B.inclusion.map T'.hom := by rw [f.w]

/-- The arrow between small-site representatives is a factorisation of the given morphism of
schemes through the two open immersions. -/
public theorem smallSiteArrow_fac
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    B.inclusion.map (smallSiteArrow B S hS f X Y hXY).left ≫
        B.inclusion.map Y.obj.hom =
      B.inclusion.map X.obj.hom ≫ B.inclusion.map f.left := by
  let i := B.inclusion.map X.obj.hom
  let j := B.inclusion.map Y.obj.hom
  let g := (BigZariskiOver.toScheme B S hS).map f
  have hset : Set.range (i ≫ g) ⊆ Set.range j := smallSiteArrow_range_subset B S hS f X Y hXY
  let ℓ := IsOpenImmersion.lift j (i ≫ g) hset
  change B.inclusion.map (B.inclusion.preimage ℓ) ≫ j = i ≫ B.inclusion.map f.left
  rw [B.inclusion.map_preimage]
  exact IsOpenImmersion.lift_fac j (i ≫ g) hset

/-- Opens contained in the preimage of an open have representatives with the same containment. -/
private theorem smallOpenObject_le_preimage
    {T T' : BigZariskiOver B S hS} (φ : T'.left.1 ⟶ T.left.1)
    {U : T'.left.1.Opens} {V : T.left.1.Opens} (h : U ≤ (Opens.map φ.base).obj V) :
    (smallZariskiToOpens B T'.left.1 T'.left.2).obj (smallOpenObject B S hS T' U) ≤
      (Opens.map φ.base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj (smallOpenObject B S hS T V)) := by
  rwa [smallOpenObject_toOpens, smallOpenObject_toOpens]

/-- The open-site maps commute with restrictions in both variables. -/
private theorem smallSiteArrow_naturality
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    {X X' : SmallZariski B T'.left.1 T'.left.2}
    {Y Y' : SmallZariski B T.left.1 T.left.2}
    (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y))
    (hX'Y' : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X' ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y')) :
    smallSiteArrow B S hS f X' Y' hX'Y' ≫
        (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).map gY =
      (smallZariskiToBigZariskiFunctor B T'.left ⟨S, hS⟩ T'.hom).map gX ≫
        smallSiteArrow B S hS f X Y hXY := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  apply (cancel_mono (B.inclusion.map Y.obj.hom)).mp
  simp only [Over.comp_left, B.inclusion.map_comp]
  have ha' := smallSiteArrow_fac B S hS f X' Y' hX'Y'
  have ha := smallSiteArrow_fac B S hS f X Y hXY
  have hg : ∀ (T : BigZariskiOver B S hS) {X X' : SmallZariski B T.left.1 T.left.2}
      (g : X' ⟶ X), B.inclusion.map g.hom.left ≫ B.inclusion.map X.obj.hom =
        B.inclusion.map X'.obj.hom := fun T X X' g => by
    simpa [smallZariskiOpenImmersion, SmallZariski.toScheme] using
      smallZariskiOpenImmersion_comp B T.left.1 T.left.2 g
  have hgy := hg T gY
  have hgx := hg T' gX
  calc
    B.inclusion.map (smallSiteArrow B S hS f X' Y' hX'Y').left ≫
        (B.inclusion.map gY.hom.left ≫ B.inclusion.map Y.obj.hom) =
      B.inclusion.map (smallSiteArrow B S hS f X' Y' hX'Y').left ≫
        B.inclusion.map Y'.obj.hom := by rw [hgy]
    _ = B.inclusion.map X'.obj.hom ≫ B.inclusion.map f.left := ha'
    _ = (B.inclusion.map gX.hom.left ≫ B.inclusion.map X.obj.hom) ≫
        B.inclusion.map f.left := by rw [hgx]
    _ = B.inclusion.map gX.hom.left ≫
        (B.inclusion.map (smallSiteArrow B S hS f X Y hXY).left ≫
          B.inclusion.map Y.obj.hom) := by
      rw [ha]
      simp [Category.assoc]

/-- At each scheme, canonical restriction is inverse image along the
small-to-big morphism of topoi, followed by the small-Zariski comparison. -/
public noncomputable def canonicalSmallSheaf
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) :
    Sheaf (Opens.grothendieckTopology T.left.1.toTopCat) (Type (max u v)) := by
  let := smallZariskiToBigZariskiFunctor_isContinuous
    B T.left ⟨S, hS⟩ T.hom
  exact (smallZariskiSheafEquiv B T.left.1 T.left.2).functor.obj
    (((smallZariskiToBigZariskiFunctor B T.left
      ⟨S, hS⟩ T.hom).sheafPushforwardContinuous (Type (max u v))
        (SmallZariski.topology B T.left.1 T.left.2)
        (BigZariskiOver.topology B S hS)).obj F)

/-- Canonical small-site restriction, functorial in the big-site sheaf. -/
public noncomputable def canonicalSmallSheafFunctor
    (T : BigZariskiOver B S hS) :
    Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)) ⥤
      Sheaf (Opens.grothendieckTopology T.left.1.toTopCat) (Type (max u v)) := by
  let := smallZariskiToBigZariskiFunctor_isContinuous
    B T.left ⟨S, hS⟩ T.hom
  exact (smallZariskiToBigZariskiFunctor B T.left
      ⟨S, hS⟩ T.hom).sheafPushforwardContinuous (Type (max u v))
        (SmallZariski.topology B T.left.1 T.left.2)
        (BigZariskiOver.topology B S hS) ⋙
      (smallZariskiSheafEquiv B T.left.1 T.left.2).functor

/-- Sections of the canonical small-site sheaf over an open subset of `T` are the sections of
the big-site sheaf at the corresponding open subscheme of `T` over `S`. -/
public noncomputable def canonicalSmallOpenSectionsIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) (U : T.left.1.Opens) :
    (canonicalSmallSheaf B S hS F T).1.obj (op U) ≅
      F.1.obj (op ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).obj
        ((smallZariskiSiteEquiv B T.left.1 T.left.2).inverse.obj U))) := by
  let := smallZariskiToBigZariskiFunctor_isContinuous
    B T.left ⟨S, hS⟩ T.hom
  let G := (smallZariskiToBigZariskiFunctor B T.left
    ⟨S, hS⟩ T.hom).sheafPushforwardContinuous (Type (max u v))
      (SmallZariski.topology B T.left.1 T.left.2)
      (BigZariskiOver.topology B S hS)
  let X := (smallZariskiSiteEquiv B T.left.1 T.left.2).inverse.obj U
  let ρ := (smallZariskiToBigZariskiFunctor B T.left
    ⟨S, hS⟩ T.hom).sheafPushforwardContinuousCompSheafToPresheafIso
      (Type (max u v)) (SmallZariski.topology B T.left.1 T.left.2)
      (BigZariskiOver.topology B S hS)
  change (G.obj F).1.obj (op X) ≅
    F.1.obj (op ((smallZariskiToBigZariskiFunctor B T.left
      ⟨S, hS⟩ T.hom).obj X))
  exact asIso ((ρ.hom.app F).app (op X))

private theorem canonicalSmallOpenSectionsIso_naturality
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) (T : BigZariskiOver B S hS) (U : T.left.1.Opens) :
    (canonicalSmallOpenSectionsIso B S hS F T U).hom ≫
        α.1.app (op ((smallZariskiToBigZariskiFunctor B T.left
          ⟨S, hS⟩ T.hom).obj
          ((smallZariskiSiteEquiv B T.left.1 T.left.2).inverse.obj U))) =
      ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op U) ≫
        (canonicalSmallOpenSectionsIso B S hS G T U).hom :=
  rfl

/-- The section comparison also applies to a small-site object before choosing
its corresponding open. -/
public noncomputable def canonicalSmallSiteSectionsIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.1 T.left.2) :
    (canonicalSmallSheaf B S hS F T).1.obj
        (op ((smallZariskiToOpens B T.left.1 T.left.2).obj X)) ≅
      F.1.obj (op ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).obj X)) := by
  let E := smallZariskiSiteEquiv B T.left.1 T.left.2
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let U := (smallZariskiToOpens B T.left.1 T.left.2).obj X
  have e : X ≅ E.inverse.obj U := E.unitIso.app X
  exact (canonicalSmallOpenSectionsIso B S hS F T U).trans
    (F.1.mapIso (j.mapIso e).op)

private theorem canonicalSmallSiteSectionsIso_naturality
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) (T : BigZariskiOver B S hS)
    (X : SmallZariski B T.left.1 T.left.2) :
    (canonicalSmallSiteSectionsIso B S hS F T X).hom ≫
        α.1.app (op ((smallZariskiToBigZariskiFunctor B T.left
          ⟨S, hS⟩ T.hom).obj X)) =
      ((canonicalSmallSheafFunctor B S hS T).map α).1.app
          (op ((smallZariskiToOpens B T.left.1 T.left.2).obj X)) ≫
        (canonicalSmallSiteSectionsIso B S hS G T X).hom := by
  let E := smallZariskiSiteEquiv B T.left.1 T.left.2
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let U := (smallZariskiToOpens B T.left.1 T.left.2).obj X
  let e := E.unitIso.app X
  let q := (j.mapIso e).op
  have hOpen := canonicalSmallOpenSectionsIso_naturality B S hS α T U
  have hα := (α.1).naturality q.hom
  dsimp [canonicalSmallSiteSectionsIso]
  cat_disch

/-- The open-section identification commutes with restriction between opens. -/
private theorem canonicalSmallOpenSectionsIso_map
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    {U V : T.left.1.Opens} (hUV : (U : Opens T.left.1.carrier) ≤ V)
    (s : (canonicalSmallSheaf B S hS F T).1.obj (op V)) :
    (canonicalSmallOpenSectionsIso B S hS F T U).hom
        ((canonicalSmallSheaf B S hS F T).1.map (homOfLE hUV).op s) =
      F.1.map ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).map
          ((smallZariskiSiteEquiv B T.left.1 T.left.2).inverse.map
            (homOfLE hUV))).op
        ((canonicalSmallOpenSectionsIso B S hS F T V).hom s) := by
  let := smallZariskiToBigZariskiFunctor_isContinuous
    B T.left ⟨S, hS⟩ T.hom
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let E := smallZariskiSiteEquiv B T.left.1 T.left.2
  let G := j.sheafPushforwardContinuous (Type (max u v))
    (SmallZariski.topology B T.left.1 T.left.2)
    (BigZariskiOver.topology B S hS)
  let ρ := j.sheafPushforwardContinuousCompSheafToPresheafIso
    (Type (max u v)) (SmallZariski.topology B T.left.1 T.left.2)
    (BigZariskiOver.topology B S hS)
  change ((ρ.hom.app F).app (op (E.inverse.obj U)))
      ((G.obj F).1.map (E.inverse.map (homOfLE hUV)).op s) =
    F.1.map (j.map (E.inverse.map (homOfLE hUV))).op
      (((ρ.hom.app F).app (op (E.inverse.obj V))) s)
  exact NatTrans.naturality_apply (ρ.hom.app F)
    (E.inverse.map (homOfLE hUV)).op s

/-- The comparison is natural with respect to a morphism in the small site. -/
private theorem canonicalSmallSiteSectionsIso_map
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    {X X' : SmallZariski B T.left.1 T.left.2} (k : X' ⟶ X)
    (s : (canonicalSmallSheaf B S hS F T).1.obj
      (op ((smallZariskiToOpens B T.left.1 T.left.2).obj X))) :
    (canonicalSmallSiteSectionsIso B S hS F T X').hom
      ((canonicalSmallSheaf B S hS F T).1.map
        ((smallZariskiToOpens B T.left.1 T.left.2).map k).op s) =
      F.1.map ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).map k).op
        ((canonicalSmallSiteSectionsIso B S hS F T X).hom s) := by
  let E := smallZariskiSiteEquiv B T.left.1 T.left.2
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let U := E.functor.obj X
  let U' := E.functor.obj X'
  let t : E.functor.obj X' ⟶ E.functor.obj X := E.functor.map k
  let e := E.unitIso.app X
  let e' := E.unitIso.app X'
  have hfun : E.functor = smallZariskiToOpens B T.left.1 T.left.2 := rfl
  have hmap := canonicalSmallOpenSectionsIso_map B S hS F T t.le s
  have ht : t = homOfLE t.le := Subsingleton.elim _ _
  rw [← ht] at hmap
  have hmap' : (canonicalSmallOpenSectionsIso B S hS F T U').hom
      ((canonicalSmallSheaf B S hS F T).1.map t.op s) =
      F.1.map (j.map (E.inverse.map t)).op
        ((canonicalSmallOpenSectionsIso B S hS F T U).hom s) := by
    simpa [U, U', hfun, j] using hmap
  change (F.1.mapIso (j.mapIso e').op).hom
      ((canonicalSmallOpenSectionsIso B S hS F T U').hom
        ((canonicalSmallSheaf B S hS F T).1.map t.op s)) = _
  rw [hmap']
  change F.1.map (j.map e'.hom).op
      (F.1.map (j.map (E.inverse.map t)).op
        ((canonicalSmallOpenSectionsIso B S hS F T U).hom s)) = _
  have hn := E.unitIso.hom.naturality k
  change k ≫ e.hom = e'.hom ≫ E.inverse.map (E.functor.map k) at hn
  have hmaps :
      F.1.map (j.map (E.inverse.map t)).op ≫ F.1.map (j.map e'.hom).op =
        F.1.map (j.map e.hom).op ≫ F.1.map (j.map k).op := by
    calc
      _ = F.1.map ((j.map (E.inverse.map t)).op ≫ (j.map e'.hom).op) :=
        (F.1.map_comp _ _).symm
      _ = F.1.map ((j.map (e'.hom ≫ E.inverse.map t)).op) := by simp
      _ = F.1.map ((j.map (k ≫ e.hom)).op) := by rw [← hn]
      _ = _ := by simp
  change (F.1.map (j.map (E.inverse.map t)).op ≫
      F.1.map (j.map e'.hom).op)
      ((canonicalSmallOpenSectionsIso B S hS F T U).hom s) =
    (F.1.map (j.map e.hom).op ≫ F.1.map (j.map k).op)
      ((canonicalSmallOpenSectionsIso B S hS F T U).hom s)
  exact congrArg (fun g => g ((canonicalSmallOpenSectionsIso B S hS F T U).hom s)) hmaps

/-- The comparison is natural with respect to a morphism in the small site, as a square. -/
private theorem canonicalSmallSiteSectionsIso_map_comp
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    {X X' : SmallZariski B T.left.1 T.left.2} (k : X' ⟶ X) :
    (canonicalSmallSheaf B S hS F T).1.map
        ((smallZariskiToOpens B T.left.1 T.left.2).map k).op ≫
      (canonicalSmallSiteSectionsIso B S hS F T X').hom =
    (canonicalSmallSiteSectionsIso B S hS F T X).hom ≫
      F.1.map ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).map k).op := by
  ext s
  exact canonicalSmallSiteSectionsIso_map B S hS F T k s

/-- Section values at the chosen representative of an open are canonically
identified with values of the big-site sheaf at its image. -/
public noncomputable def canonicalSmallRepresentativeSectionsIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    (U : T.left.1.Opens)
    (X : SmallZariski B T.left.1 T.left.2)
    (hX : (smallZariskiToOpens B T.left.1 T.left.2).obj X = U) :
    (canonicalSmallSheaf B S hS F T).1.obj (op U) ≅
      F.1.obj (op ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).obj X)) :=
  ((canonicalSmallSheaf B S hS F T).1.mapIso (eqToIso hX).op).trans
    (canonicalSmallSiteSectionsIso B S hS F T X)

private theorem canonicalSmallRepresentativeSectionsIso_naturality
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) (T : BigZariskiOver B S hS)
    (U : T.left.1.Opens) (X : SmallZariski B T.left.1 T.left.2)
    (hX : (smallZariskiToOpens B T.left.1 T.left.2).obj X = U) :
    (canonicalSmallRepresentativeSectionsIso B S hS F T U X hX).hom ≫
        α.1.app (op ((smallZariskiToBigZariskiFunctor B T.left
          ⟨S, hS⟩ T.hom).obj X)) =
      ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op U) ≫
        (canonicalSmallRepresentativeSectionsIso B S hS G T U X hX).hom := by
  let q := (eqToIso hX).op
  have hα := ((canonicalSmallSheafFunctor B S hS T).map α).1.naturality q.hom
  have hsite := canonicalSmallSiteSectionsIso_naturality B S hS α T X
  dsimp [canonicalSmallRepresentativeSectionsIso]
  cat_disch

/-- The chosen small-site representative of the whole space of `T` is `T` itself. -/
public noncomputable def canonicalSmallTopRepresentativeIso
    (T : BigZariskiOver B S hS) :
    (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).obj
        (smallOpenObject B S hS T ⊤) ≅ T := by
  let X := smallOpenObject B S hS T ⊤
  have htop : (B.inclusion.map X.obj.hom).opensRange = ⊤ := by
    simpa [X, smallZariskiToOpens,
      smallZariskiOpenImmersion] using
        smallOpenObject_toOpens B S hS T ⊤
  have : IsIso (B.inclusion.map X.obj.hom) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ htop
  let e := asIso (B.inclusion.map X.obj.hom)
  let e' := B.inclusion.preimageIso e
  have he' : e'.hom = X.obj.hom := by
    change B.inclusion.preimage (B.inclusion.map X.obj.hom) = X.obj.hom
    exact B.inclusion.preimage_map _
  refine Over.isoMk e' ?_
  rw [he']
  rfl

/-- Global sections of the canonical small-site sheaf on `T` are the sections of the big-site
sheaf at `T`. -/
public noncomputable def canonicalSmallTopSectionsIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) :
    (canonicalSmallSheaf B S hS F T).1.obj (op ⊤) ≅ F.1.obj (op T) :=
  (canonicalSmallRepresentativeSectionsIso B S hS F T ⊤
      (smallOpenObject B S hS T ⊤) (smallOpenObject_toOpens B S hS T ⊤)).trans
    (F.1.mapIso (canonicalSmallTopRepresentativeIso B S hS T).symm.op)

/-- The identification of global sections is natural in the big-site sheaf. -/
public theorem canonicalSmallTopSectionsIso_naturality
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) (T : BigZariskiOver B S hS) :
    (canonicalSmallTopSectionsIso B S hS F T).hom ≫ α.1.app (op T) =
      ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op ⊤) ≫
        (canonicalSmallTopSectionsIso B S hS G T).hom := by
  let X := smallOpenObject B S hS T ⊤
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let r := canonicalSmallTopRepresentativeIso B S hS T
  let repF := canonicalSmallRepresentativeSectionsIso B S hS F T ⊤ X
    (smallOpenObject_toOpens B S hS T ⊤)
  let repG := canonicalSmallRepresentativeSectionsIso B S hS G T ⊤ X
    (smallOpenObject_toOpens B S hS T ⊤)
  let q := r.symm.op.hom
  have hrep := canonicalSmallRepresentativeSectionsIso_naturality B S hS α T ⊤ X
    (smallOpenObject_toOpens B S hS T ⊤)
  have hα := (α.1).naturality q
  change (repF.hom ≫ F.1.map q) ≫ α.1.app (op T) =
    ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op ⊤) ≫
      (repG.hom ≫ G.1.map q)
  simp only [Category.assoc]
  rw [hα]
  simp only [← Category.assoc]
  rw [hrep]
  rfl

private noncomputable def smallOpenSiteArrow
    {T : BigZariskiOver B S hS} {U V : T.left.1.Opens}
    (hUV : (U : Opens T.left.1.carrier) ≤ V) :
    smallOpenObject B S hS T U ⟶ smallOpenObject B S hS T V :=
  (smallZariskiToOpens B T.left.1 T.left.2).preimage
    (eqToHom (smallOpenObject_toOpens B S hS T U) ≫ homOfLE hUV ≫
      eqToHom (smallOpenObject_toOpens B S hS T V).symm)

private theorem smallOpenSiteArrow_map
    {T : BigZariskiOver B S hS} {U V : T.left.1.Opens}
    (hUV : (U : Opens T.left.1.carrier) ≤ V) :
    (smallZariskiToOpens B T.left.1 T.left.2).map
      (smallOpenSiteArrow B S hS hUV) =
        eqToHom (smallOpenObject_toOpens B S hS T U) ≫ homOfLE hUV ≫
          eqToHom (smallOpenObject_toOpens B S hS T V).symm := by
  dsimp [smallOpenSiteArrow]
  rw [Functor.map_preimage]

/-- The representative section comparison is natural for inclusions of opens. -/
private theorem canonicalSmallRepresentativeSectionsIso_map
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    {U V : T.left.1.Opens} (hUV : (U : Opens T.left.1.carrier) ≤ V)
    (s : (canonicalSmallSheaf B S hS F T).1.obj (op V)) :
    (canonicalSmallRepresentativeSectionsIso B S hS F T U
      (smallOpenObject B S hS T U) (smallOpenObject_toOpens B S hS T U)).hom
      ((canonicalSmallSheaf B S hS F T).1.map (homOfLE hUV).op s) =
    F.1.map ((smallZariskiToBigZariskiFunctor B T.left
      ⟨S, hS⟩ T.hom).map (smallOpenSiteArrow B S hS hUV)).op
      ((canonicalSmallRepresentativeSectionsIso B S hS F T V
        (smallOpenObject B S hS T V) (smallOpenObject_toOpens B S hS T V)).hom s) := by
  let E := smallZariskiToOpens B T.left.1 T.left.2
  let j := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  let X := smallOpenObject B S hS T U
  let Y := smallOpenObject B S hS T V
  let eX := smallOpenObject_toOpens B S hS T U
  let eY := smallOpenObject_toOpens B S hS T V
  let g := smallOpenSiteArrow B S hS hUV
  let sY := (canonicalSmallSheaf B S hS F T).1.map (eqToHom eY).op s
  have hsite := canonicalSmallSiteSectionsIso_map B S hS F T g sY
  have hfac : E.map g = eqToHom eX ≫ homOfLE hUV ≫ eqToHom eY.symm :=
    smallOpenSiteArrow_map B S hS hUV
  have hcat : E.map g ≫ eqToHom eY = eqToHom eX ≫ homOfLE hUV := by
    rw [hfac]
    simp
  have hcatop : (eqToHom eY).op ≫ (E.map g).op =
      (homOfLE hUV).op ≫ (eqToHom eX).op := by
    simpa only [op_comp] using congrArg (fun q => q.op) hcat
  have hcatmap :
      (canonicalSmallSheaf B S hS F T).1.map (homOfLE hUV).op ≫
          (canonicalSmallSheaf B S hS F T).1.map (eqToHom eX).op =
        (canonicalSmallSheaf B S hS F T).1.map (eqToHom eY).op ≫
          (canonicalSmallSheaf B S hS F T).1.map (E.map g).op := by
    rw [← (canonicalSmallSheaf B S hS F T).1.map_comp,
      ← (canonicalSmallSheaf B S hS F T).1.map_comp]
    exact congrArg ((canonicalSmallSheaf B S hS F T).1.map) hcatop
  change (canonicalSmallSiteSectionsIso B S hS F T X).hom
      ((canonicalSmallSheaf B S hS F T).1.map (eqToHom eX).op
        ((canonicalSmallSheaf B S hS F T).1.map (homOfLE hUV).op s)) =
    F.1.map (j.map g).op
      ((canonicalSmallSiteSectionsIso B S hS F T Y).hom sY)
  calc
    _ = (canonicalSmallSiteSectionsIso B S hS F T X).hom
        ((canonicalSmallSheaf B S hS F T).1.map (E.map g).op sY) :=
          congrArg
            (fun m => (canonicalSmallSiteSectionsIso B S hS F T X).hom (m s)) hcatmap
    _ = F.1.map (j.map g).op
        ((canonicalSmallSiteSectionsIso B S hS F T Y).hom sY) := hsite

private theorem canonicalSmallRepresentativeSectionsIso_map_comp
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS)
    {U V : T.left.1.Opens} (hUV : (U : Opens T.left.1.carrier) ≤ V) :
    (canonicalSmallSheaf B S hS F T).1.map (homOfLE hUV).op ≫
        (canonicalSmallRepresentativeSectionsIso B S hS F T U
          (smallOpenObject B S hS T U) (smallOpenObject_toOpens B S hS T U)).hom =
      (canonicalSmallRepresentativeSectionsIso B S hS F T V
          (smallOpenObject B S hS T V) (smallOpenObject_toOpens B S hS T V)).hom ≫
        F.1.map ((smallZariskiToBigZariskiFunctor B T.left
          ⟨S, hS⟩ T.hom).map (smallOpenSiteArrow B S hS hUV)).op := by
  ext s
  exact canonicalSmallRepresentativeSectionsIso_map B S hS F T hUV s

private theorem smallSiteArrow_naturality_map
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    {X X' : SmallZariski B T'.left.1 T'.left.2}
    {Y Y' : SmallZariski B T.left.1 T.left.2}
    (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y))
    (hX'Y' : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X' ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y')) :
    F.1.map ((smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).map gY).op ≫
        F.1.map (smallSiteArrow B S hS f X' Y' hX'Y').op =
      F.1.map (smallSiteArrow B S hS f X Y hXY).op ≫
        F.1.map ((smallZariskiToBigZariskiFunctor B T'.left ⟨S, hS⟩ T'.hom).map gX).op := by
  rw [← F.1.map_comp, ← F.1.map_comp]
  congr 1
  simpa using congrArg (fun q => q.op) (smallSiteArrow_naturality B S hS f gX gY hXY hX'Y')

/-- The map on open sections induced by a map of schemes, computed on small-site
representatives using the corresponding arrow of the big site. -/
public noncomputable def canonicalSmallPairMap
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : T'.left.1.Opens) (V : T.left.1.Opens)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hX : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X = U)
    (hY : (smallZariskiToOpens B T.left.1 T.left.2).obj Y = V)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    (canonicalSmallSheaf B S hS F T).1.obj (op V) ⟶
      (canonicalSmallSheaf B S hS F T').1.obj (op U) := by
  let a := smallSiteArrow B S hS f X Y hXY
  exact (canonicalSmallRepresentativeSectionsIso B S hS F T V Y hY).hom ≫
    F.1.map a.op ≫
      (canonicalSmallRepresentativeSectionsIso B S hS F T' U X hX).inv

/-- On the open sets represented by small-site objects, the section maps commute
with restrictions in both variables. -/
private noncomputable def canonicalSmallSitePairMap
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    (canonicalSmallSheaf B S hS F T).1.obj
      (op ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) ⟶
    (canonicalSmallSheaf B S hS F T').1.obj
      (op ((smallZariskiToOpens B T'.left.1 T'.left.2).obj X)) :=
  (canonicalSmallSiteSectionsIso B S hS F T Y).hom ≫
    F.1.map (smallSiteArrow B S hS f X Y hXY).op ≫
      (canonicalSmallSiteSectionsIso B S hS F T' X).inv

private theorem canonicalSmallSitePairMap_naturality
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    {X X' : SmallZariski B T'.left.1 T'.left.2}
    {Y Y' : SmallZariski B T.left.1 T.left.2}
    (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y))
    (hX'Y' : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X' ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y')) :
    (canonicalSmallSheaf B S hS F T).1.map
        ((smallZariskiToOpens B T.left.1 T.left.2).map gY).op ≫
      canonicalSmallSitePairMap B S hS F f X' Y' hX'Y' =
    canonicalSmallSitePairMap B S hS F f X Y hXY ≫
      (canonicalSmallSheaf B S hS F T').1.map
        ((smallZariskiToOpens B T'.left.1 T'.left.2).map gX).op := by
  let a := smallSiteArrow B S hS f X Y hXY
  let a' := smallSiteArrow B S hS f X' Y' hX'Y'
  let jX := smallZariskiToBigZariskiFunctor B T'.left ⟨S, hS⟩ T'.hom
  let jY := smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom
  have hsquare := smallSiteArrow_naturality B S hS f gX gY hXY hX'Y'
  have hmapY := canonicalSmallSiteSectionsIso_map_comp B S hS F T gY
  have hmapX := canonicalSmallSiteSectionsIso_map_comp B S hS F T' gX
  apply (cancel_mono (canonicalSmallSiteSectionsIso B S hS F T' X').hom).mp
  dsimp [canonicalSmallSitePairMap, a, a']
  simp only [Category.assoc, Iso.inv_hom_id]
  rw [← Category.assoc, hmapY]
  rw [← Category.assoc, hmapX]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc, Category.comp_id,
    Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
  have hF := smallSiteArrow_naturality_map B S hS F f gX gY hXY hX'Y'
  dsimp [a, a', jX, jY] at hF
  dsimp [jX, jY]
  rw [hF]

private theorem canonicalSmallPairMap_naturality
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    {U U' : T'.left.1.Opens} {V V' : T.left.1.Opens}
    (hU : (U' : Opens T'.left.1.carrier) ≤ U)
    (hV : (V' : Opens T.left.1.carrier) ≤ V)
    (hUV : U ≤ (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj V)
    (hU'V' : U' ≤ (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj V') :
    (canonicalSmallSheaf B S hS F T).1.map (homOfLE hV).op ≫
      canonicalSmallPairMap B S hS F f U' V'
        (smallOpenObject B S hS T' U') (smallOpenObject B S hS T V')
        (smallOpenObject_toOpens B S hS T' U')
        (smallOpenObject_toOpens B S hS T V') (by
          simpa only [smallOpenObject_toOpens] using hU'V') =
    canonicalSmallPairMap B S hS F f U V
        (smallOpenObject B S hS T' U) (smallOpenObject B S hS T V)
        (smallOpenObject_toOpens B S hS T' U)
        (smallOpenObject_toOpens B S hS T V) (by
          simpa only [smallOpenObject_toOpens] using hUV) ≫
      (canonicalSmallSheaf B S hS F T').1.map (homOfLE hU).op := by
  let X := smallOpenObject B S hS T' U
  let X' := smallOpenObject B S hS T' U'
  let Y := smallOpenObject B S hS T V
  let Y' := smallOpenObject B S hS T V'
  have hXY := smallOpenObject_le_preimage B S hS ((BigZariskiOver.toScheme B S hS).map f) hUV
  have hX'Y' := smallOpenObject_le_preimage B S hS ((BigZariskiOver.toScheme B S hS).map f) hU'V'
  apply (cancel_mono
    (canonicalSmallRepresentativeSectionsIso B S hS F T' U' X'
      (smallOpenObject_toOpens B S hS T' U')).hom).mp
  dsimp [canonicalSmallPairMap, X, X', Y, Y']
  simp only [Category.assoc]
  rw [← Category.assoc, canonicalSmallRepresentativeSectionsIso_map_comp B S hS F T hV]
  simp only [Category.assoc]
  have hF := smallSiteArrow_naturality_map B S hS F f (smallOpenSiteArrow B S hS hU)
    (smallOpenSiteArrow B S hS hV) hXY hX'Y'
  dsimp [X, X', Y, Y', smallZariskiToBigZariskiFunctor] at hF
  dsimp [smallZariskiToBigZariskiFunctor]
  slice_lhs 2 3 => rw [hF]
  simp only [Category.assoc]
  rw [← Category.assoc, canonicalSmallRepresentativeSectionsIso_map_comp B S hS F T' hU]
  simp [Category.assoc]

/-- The section maps induced by a morphism of schemes over `S` are natural in the big-site
sheaf. -/
public theorem canonicalSmallPairMap_naturality_in_F
    {F G : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v))}
    (α : F ⟶ G) {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    (U : T'.left.1.Opens) (V : T.left.1.Opens)
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hX : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X = U)
    (hY : (smallZariskiToOpens B T.left.1 T.left.2).obj Y = V)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map ((BigZariskiOver.toScheme B S hS).map f).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y)) :
    ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op V) ≫
        canonicalSmallPairMap B S hS G f U V X Y hX hY hXY =
      canonicalSmallPairMap B S hS F f U V X Y hX hY hXY ≫
        ((canonicalSmallSheafFunctor B S hS T').map α).1.app (op U) := by
  let a := smallSiteArrow B S hS f X Y hXY
  let iFY := canonicalSmallRepresentativeSectionsIso B S hS F T V Y hY
  let iGY := canonicalSmallRepresentativeSectionsIso B S hS G T V Y hY
  let iFX := canonicalSmallRepresentativeSectionsIso B S hS F T' U X hX
  let iGX := canonicalSmallRepresentativeSectionsIso B S hS G T' U X hX
  have hYα := canonicalSmallRepresentativeSectionsIso_naturality B S hS α T V Y hY
  have hXα := canonicalSmallRepresentativeSectionsIso_naturality B S hS α T' U X hX
  have hYα' : iFY.hom ≫ α.1.app
      (op ((smallZariskiToBigZariskiFunctor B T.left
        ⟨S, hS⟩ T.hom).obj Y)) =
      ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op V) ≫ iGY.hom := hYα
  have hXα' : iFX.hom ≫ α.1.app
      (op ((smallZariskiToBigZariskiFunctor B T'.left
        ⟨S, hS⟩ T'.hom).obj X)) =
      ((canonicalSmallSheafFunctor B S hS T').map α).1.app (op U) ≫ iGX.hom := hXα
  have hα := (α.1).naturality a.op
  have hXinv : α.1.app
      (op ((smallZariskiToBigZariskiFunctor B T'.left
        ⟨S, hS⟩ T'.hom).obj X)) ≫ iGX.inv =
      iFX.inv ≫ ((canonicalSmallSheafFunctor B S hS T').map α).1.app (op U) := by
    apply (cancel_mono iGX.hom).mp
    calc
      _ = α.1.app
          (op ((smallZariskiToBigZariskiFunctor B T'.left
            ⟨S, hS⟩ T'.hom).obj X)) := by simp
      _ = iFX.inv ≫ iFX.hom ≫ α.1.app
          (op ((smallZariskiToBigZariskiFunctor B T'.left
            ⟨S, hS⟩ T'.hom).obj X)) := by simp
      _ = iFX.inv ≫ ((canonicalSmallSheafFunctor B S hS T').map α).1.app
          (op U) ≫ iGX.hom := by
        rw [hXα']
        exact Category.assoc _ _ _
      _ = _ := (Category.assoc _ _ _).symm
  change ((canonicalSmallSheafFunctor B S hS T).map α).1.app (op V) ≫
      (iGY.hom ≫ G.1.map a.op ≫ iGX.inv) =
      (iFY.hom ≫ F.1.map a.op ≫ iFX.inv) ≫
      ((canonicalSmallSheafFunctor B S hS T').map α).1.app (op U)
  have h1 := congrArg (fun q => q ≫ G.1.map a.op ≫ iGX.inv) hYα'.symm
  have h2 := congrArg (fun q => iFY.hom ≫ q ≫ iGX.inv) hα.symm
  have h3 := congrArg (fun q => iFY.hom ≫ F.1.map a.op ≫ q) hXinv
  convert h1.trans (h2.trans h3) using 1
  cat_disch

/-- The compatible family of section maps that the canonical small-site sheaves carry along a
morphism of schemes over `S`. -/
public noncomputable def canonicalSmallPullbackFamily
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T) :
    TopCat.Sheaf.InverseImageSectionFamily.{u, v} (B.inclusion.map f.left).base
      (canonicalSmallSheaf B S hS F T) (canonicalSmallSheaf B S hS F T') where
  app U V hUV :=
    have hUV' : U ≤ (Opens.map
        ((BigZariskiOver.toScheme B S hS).map f).base).obj V := by
      simpa [BigZariskiOver.toScheme] using hUV
    canonicalSmallPairMap B S hS F f U V
      (smallOpenObject B S hS T' U) (smallOpenObject B S hS T V)
      (smallOpenObject_toOpens B S hS T' U)
      (smallOpenObject_toOpens B S hS T V) (by
        rwa [smallOpenObject_toOpens, smallOpenObject_toOpens])
  naturality {U U'} {V V'} hU hV hUV hU'V' s := by
    have hUV' : U ≤ (Opens.map
        ((BigZariskiOver.toScheme B S hS).map f).base).obj V := by
      simpa [BigZariskiOver.toScheme] using hUV
    have hU'V'' : U' ≤ (Opens.map
        ((BigZariskiOver.toScheme B S hS).map f).base).obj V' := by
      simpa [BigZariskiOver.toScheme] using hU'V'
    have h := canonicalSmallPairMap_naturality B S hS F f hU.le hV.le hUV' hU'V''
    exact congrArg (fun α => α s) h

private theorem smallSiteArrow_comp
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (X : SmallZariski B T''.left.1 T''.left.2)
    (Y : SmallZariski B T'.left.1 T'.left.2)
    (Z : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T''.left.1 T''.left.2).obj X ≤
      (Opens.map (B.inclusion.map g.left).base).obj
        ((smallZariskiToOpens B T'.left.1 T'.left.2).obj Y))
    (hYZ : (smallZariskiToOpens B T'.left.1 T'.left.2).obj Y ≤
      (Opens.map (B.inclusion.map f.left).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Z))
    (hXZ : (smallZariskiToOpens B T''.left.1 T''.left.2).obj X ≤
      (Opens.map (B.inclusion.map (g ≫ f).left).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Z)) :
    smallSiteArrow B S hS g X Y hXY ≫ smallSiteArrow B S hS f Y Z hYZ =
      smallSiteArrow B S hS (g ≫ f) X Z hXZ := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  apply (cancel_mono (B.inclusion.map Z.obj.hom)).mp
  simp only [Over.comp_left, Functor.map_comp, Category.assoc]
  rw [smallSiteArrow_fac, ← Category.assoc, smallSiteArrow_fac]
  simpa only [Over.comp_left, Functor.map_comp, Category.assoc] using
    (smallSiteArrow_fac B S hS (g ≫ f) X Z hXZ).symm

/-- The compatible families of section maps compose, over any nested triple of opens. -/
public theorem canonicalSmallPullbackFamily_comp
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    {T T' T'' : BigZariskiOver B S hS} (f : T' ⟶ T) (g : T'' ⟶ T')
    (W : T''.left.1.Opens) (U : T'.left.1.Opens) (V : T.left.1.Opens)
    (hWU : W ≤ (Opens.map (B.inclusion.map g.left).base).obj U)
    (hUV : U ≤ (Opens.map (B.inclusion.map f.left).base).obj V)
    (hWV : W ≤ (Opens.map (B.inclusion.map (g ≫ f).left).base).obj V)
    (s : (canonicalSmallSheaf B S hS F T).obj.obj (op V)) :
    (canonicalSmallPullbackFamily B S hS F g).app W U hWU
      ((canonicalSmallPullbackFamily B S hS F f).app U V hUV s) =
    (canonicalSmallPullbackFamily B S hS F (g ≫ f)).app W V hWV s := by
  let X := smallOpenObject B S hS T'' W
  let Y := smallOpenObject B S hS T' U
  let Z := smallOpenObject B S hS T V
  have hX := smallOpenObject_toOpens B S hS T'' W
  have hY := smallOpenObject_toOpens B S hS T' U
  have hZ := smallOpenObject_toOpens B S hS T V
  have hXY := smallOpenObject_le_preimage B S hS (B.inclusion.map g.left) hWU
  have hYZ := smallOpenObject_le_preimage B S hS (B.inclusion.map f.left) hUV
  have hXZ := smallOpenObject_le_preimage B S hS (B.inclusion.map (g ≫ f).left) hWV
  change (canonicalSmallPairMap B S hS F f U V Y Z hY hZ hYZ ≫
    canonicalSmallPairMap B S hS F g W U X Y hX hY hXY) s =
    (canonicalSmallPairMap B S hS F (g ≫ f) W V X Z hX hZ hXZ) s
  apply congrArg (fun k : (canonicalSmallSheaf B S hS F T).obj.obj (op V) ⟶
    (canonicalSmallSheaf B S hS F T'').obj.obj (op W) => k s)
  dsimp only [canonicalSmallPairMap]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, ← op_comp, smallSiteArrow_comp]

/-- Along an open immersion, the arrow between small-site representatives is an isomorphism
as soon as the image of the source open is the target open. -/
public theorem smallSiteArrow_isIso
    {T T' : BigZariskiOver B S hS} (f : T' ⟶ T)
    [IsOpenImmersion (B.inclusion.map f.left)]
    (X : SmallZariski B T'.left.1 T'.left.2)
    (Y : SmallZariski B T.left.1 T.left.2)
    (hXY : (smallZariskiToOpens B T'.left.1 T'.left.2).obj X ≤
      (Opens.map (B.inclusion.map f.left).base).obj
        ((smallZariskiToOpens B T.left.1 T.left.2).obj Y))
    (himage : (B.inclusion.map f.left) ''
      ((smallZariskiToOpens B T'.left.1 T'.left.2).obj X : Set T'.left.1) =
      ((smallZariskiToOpens B T.left.1 T.left.2).obj Y : Set T.left.1)) :
    IsIso (smallSiteArrow B S hS f X Y hXY) := by
  let a := smallSiteArrow B S hS f X Y hXY
  let i := B.inclusion.map X.obj.hom
  let j := B.inclusion.map Y.obj.hom
  let k := B.inclusion.map a.left
  have hfac : k ≫ j = i ≫ B.inclusion.map f.left :=
    smallSiteArrow_fac B S hS f X Y hXY
  have : IsOpenImmersion (k ≫ j) := by
    rw [hfac]
    infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  have hk : Function.Surjective k := by
    intro y
    have hy : j y ∈ (smallZariskiToOpens B T.left.1 T.left.2).obj Y :=
      ⟨y, rfl⟩
    change j y ∈ ((smallZariskiToOpens B T.left.1 T.left.2).obj Y : Set T.left.1) at hy
    rw [← himage] at hy
    obtain ⟨_, ⟨z, rfl⟩, hxy⟩ := hy
    refine ⟨z, (Scheme.Hom.isOpenEmbedding j).injective ?_⟩
    calc
      j (k z) = (B.inclusion.map f.left) (i z) :=
        congrArg (fun q : X.obj.left.obj ⟶ T.left.obj => q z) hfac
      _ = j y := hxy
  have : IsIso k := by
    rw [isIso_iff_isOpenImmersion_and_epi_base]
    exact ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr hk⟩
  have : IsIso (B.inclusion.map a.left) := ‹IsIso k›
  have : IsIso a.left := isIso_of_reflects_iso a.left B.inclusion
  have : IsIso ((Over.forget _).map a) := ‹IsIso a.left›
  exact isIso_of_reflects_iso a (Over.forget _)

/-- As presheaves on the small Zariski site of `T`, the canonical small-site sheaf agrees with
the restriction of the big-site sheaf along the small-to-big functor. -/
public def canonicalSmallSiteIso
    (F : Sheaf (BigZariskiOver.topology B S hS) (Type (max u v)))
    (T : BigZariskiOver B S hS) :
    (smallZariskiToOpens B T.left.obj T.left.property).op ⋙
      (canonicalSmallSheaf B S hS F T).obj ≅
    (smallZariskiToBigZariskiFunctor B T.left ⟨S, hS⟩ T.hom).op ⋙ F.obj :=
  NatIso.ofComponents (fun X => canonicalSmallSiteSectionsIso B S hS F T X.unop) (by
    intro X Y k
    ext s
    exact canonicalSmallSiteSectionsIso_map B S hS F T k.unop s)

end AlgebraicGeometry
