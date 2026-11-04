module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDatumSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# The component modules of a descent datum are the étale restrictions of one `𝒪_X`-module

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X` whose charts are cover dense in the small étale site of `X`, and let `D` be
a descent datum for quasi-coherent modules relative to that family. Let `M` be an `𝒪_X`-module
whose restriction to the site of the charts of the members is isomorphic to a sheaf of modules
`N` whose sections over a chart `V` of `Y i` are the sections of `D.F i` over `V`, compatibly
with the restriction maps. Then for each member `i` the étale restriction of `M` to `Y i` is
isomorphic to `D.F i`, and `M` is quasi-coherent. Both hold in particular when `N` is the sheaf
of modules of the descent datum.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartIso`: the sections of the étale
  restriction of `M` to a member over a chart, identified with the sections of the component
  module.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberPerMemberIso`: the étale restriction of
  `M` to a member is isomorphic to the component module there.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberPerMemberIso_hom_val_app`: the component
  of `memberPerMemberIso` over a chart of a member is the component of the given isomorphism of
  sheaves of modules on the charts of the members.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isQuasicoherentOnSite_of_memberPerMemberIso`:
  `M` is quasi-coherent.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumSheaf_obj` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumSheaf_map`: the sections and the
  restriction maps of the sheaf of modules of a descent datum over the charts of a member are
  those of the component module.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_memberPerMemberIso`: for the sheaf of
  modules of a descent datum, there is a family of isomorphisms of the étale restrictions of `M`
  with the component modules whose components are those of the given isomorphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isQuasicoherentOnSite_of_memberDatumSheaf_iso`:
  an `𝒪_X`-module whose restriction to the charts of the members is isomorphic to the sheaf of
  modules of a descent datum is quasi-coherent.

## Implementation notes

The isomorphisms are constructed for a sheaf of modules `N` given as a variable, together with
hypotheses `hobj` and `hmap` identifying its sections and restriction maps with those of the
component modules. At the sheaf of modules of a descent datum both identifications hold by `rfl`
(`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumSheaf_obj` and
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumSheaf_map`), and the family of
isomorphisms is stated as the existence statement
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_memberPerMemberIso`.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

variable (D : DescentDatum B S hS Yi f)

/-! ### The comparison, at a sheaf of modules carried as a variable -/

section Variable

variable (N : SheafOfModules.{u} (memberRing B S hS Yi f hf))
  (hobj : ∀ (j : I) (V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C),
    N.val.obj (Opposite.op (memberPair B S hS Yi f hf j V)) = (D.F j).val.obj (Opposite.op V))
  (M : Modules.{u, u} B S hS X.1 X.2)
  (β : (memberRestriction B S hS Yi f hf).obj M ≅ N)
  (hmap : ∀ (j : I) (W V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C) (a : W ⟶ V)
      (y : ↥(N.val.obj (Opposite.op (memberPair B S hS Yi f hf j V)))),
    ModuleCat.Hom.hom (eqToHom (hobj j W))
        (N.val.map (memberDiagHom B S hS Yi f hf (i := j) (W := W) (V := V) a).op y) =
      (D.F j).val.map a.op (ModuleCat.Hom.hom (eqToHom (hobj j V)) y))

/-- Over a chart `W` of the member `Y i`, the sections of the étale restriction of `M` to `Y i`
are isomorphic to the sections of `D.F i`: the component of `β` over the corresponding object of
the site of the charts of the members, followed by the identification `hobj`. -/
def memberChartIso (i : I) (W : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).Cᵒᵖ) :
    ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).val.obj W ≅ (D.F i).val.obj W :=
  (PresheafOfModules.evaluation _
        (Opposite.op (memberPair B S hS Yi f hf i W.unop))).mapIso
      ((SheafOfModules.forget _).mapIso β) ≪≫
    eqToIso (hobj i W.unop)

/-- `.memberChartIso` is the given isomorphism over the chart of the member, followed by the
identification of its target. -/
theorem memberChartIso_hom (i : I)
    (W : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).Cᵒᵖ) :
    (memberChartIso B S hS Yi f hf D N hobj M β i W).hom =
      β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i W.unop)) ≫
        eqToHom (hobj i W.unop) :=
  rfl

/-- `.memberChartIso` on a section. -/
theorem memberChartIso_hom_apply (i : I)
    (W : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).Cᵒᵖ)
    (x : ↥(((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).val.obj W)) :
    (memberChartIso B S hS Yi f hf D N hobj M β i W).hom x =
      ModuleCat.Hom.hom (eqToHom (hobj i W.unop))
        (β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i W.unop)) x) :=
  rfl

include hmap in
/-- `.memberChartIso` commutes with the restriction maps along a morphism of charts of the
member. -/
theorem memberChartIso_naturality (i : I)
    {Z Z' : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).Cᵒᵖ} (g : Z ⟶ Z') :
    ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).val.map g ≫
        (ModuleCat.restrictScalars (((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).O)).obj.map g).hom).map
          (memberChartIso B S hS Yi f hf D N hobj M β i Z').hom =
      (memberChartIso B S hS Yi f hf D N hobj M β i Z).hom ≫ (D.F i).val.map g :=
  PresheafOfModules.naturality_of_apply _ _ g _ _ fun m =>
    (memberChartIso_hom_apply B S hS Yi f hf D N hobj M β i Z' _).trans
      ((congrArg _
          ((PresheafOfModules.naturality_apply β.hom.val
              (memberDiagHom B S hS Yi f hf
                (i := i) (W := Z'.unop) (V := Z.unop) g.unop).op m))).trans
        ((hmap i Z'.unop Z.unop g.unop _).trans
          (congrArg _ ((memberChartIso_hom_apply B S hS Yi f hf D N hobj M β i Z m).symm))))

/-- The étale restriction of `M` to the member `Y i` is isomorphic to `D.F i` as presheaves of
modules, by `.memberChartIso` over every chart. -/
def memberPerMemberIsoVal (i : I) :
    ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).val ≅ (D.F i).val :=
  PresheafOfModules.isoMk (memberChartIso B S hS Yi f hf D N hobj M β i)
    fun {_ _} g => memberChartIso_naturality B S hS Yi f hf D N hobj M β hmap i g

/-- The étale restriction of `M` to the member `Y i` is isomorphic to `D.F i`. -/
def memberPerMemberIso (i : I) :
    (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (memberPerMemberIsoVal B S hS Yi f hf D N hobj M β hmap i)

/-- Over a chart `V` of the member `Y i`, the component of `.memberPerMemberIso` is the component
of `β` over the corresponding object of the site of the charts of the members, followed by the
identification `hobj`. -/
theorem memberPerMemberIso_hom_val_app (i : I)
    (V : (smallEtaleRingedSite B S hS (Yi i).1 (Yi i).2).C) :
    (memberPerMemberIso B S hS Yi f hf D N hobj M β hmap i).hom.val.app (Opposite.op V) =
      β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)) ≫ eqToHom (hobj i V) :=
  rfl

include β hmap in
/-- The étale restriction of `M` to each member is quasi-coherent. -/
theorem isQuasicoherentOnSite_etaleModulePullback_of_memberPerMemberIso (i : I) :
    ((etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (memberPerMemberIso B S hS Yi f hf D N hobj M β hmap i).symm (D.quasicoherent i)

include β hmap in
/-- The `𝒪_X`-module `M` is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_memberPerMemberIso : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_forall_etaleModulePullback B S hS Yi f hf M fun i =>
    isQuasicoherentOnSite_etaleModulePullback_of_memberPerMemberIso
      B S hS Yi f hf D N hobj M β hmap i

end Variable

/-! ### The two identifications, at the sheaf of modules of a descent datum -/

variable (hL : MemberAbLaws B S hS Yi f hf (fun p => ↥(memberDatumObj B S hS Yi f hf D p))
    (fun _ => inferInstance)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hM : MemberModLaws B S hS Yi f hf (memberDatumObj B S hS Yi f hf D)
    (fun p q g m => (memberDatumAbTransHom B S hS Yi f hf D p q g).val.app
      (Opposite.op (chartSpaceIdChart B S hS (Yi q.unop.1) q.unop.2))
      (memberDatumAbRestrFn B S hS Yi f hf D p q g m)))
  (hsh : Presheaf.IsSheaf (memberTopology B S hS Yi f hf)
    (memberFunctorOfLawsV B S hS Yi f hf hL))

/-- The sections of the sheaf of modules of a descent datum over the chart `V` of the member
`Y j` are the sections of `D.F j` over `V`. -/
theorem memberDatumSheaf_obj (j : I)
    (V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C) :
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.obj
        (Opposite.op (memberPair B S hS Yi f hf j V)) = (D.F j).val.obj (Opposite.op V) :=
  rfl

/-- The morphism induced by the identification `.memberDatumSheaf_obj` is the identity. -/
theorem eqToHom_memberDatumSheaf_obj (j : I)
    (V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C) :
    eqToHom (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh j V) = 𝟙 _ :=
  rfl

/-- `AlgebraicGeometry.Space.QuasiCoherentDescent.memberDatumAbFunctor_map_memberDiagHom` with the
two charts given as objects of the small étale ringed site of the member. -/
theorem memberDatumAbFunctor_map_memberDiagHom_site (j : I)
    (W V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C) (a : W ⟶ V)
    (m : ↥((memberFunctorOfLawsV B S hS Yi f hf hL).obj
      (Opposite.op (memberPair B S hS Yi f hf j V)))) :
    @Eq ↥((memberFunctorOfLawsV B S hS Yi f hf hL).obj
        (Opposite.op (memberPair B S hS Yi f hf j W)))
      ((memberFunctorOfLawsV B S hS Yi f hf hL).map
        (memberDiagHom B S hS Yi f hf (i := j) (W := W) (V := V) a).op m)
      (ModuleCat.Hom.hom ((D.F j).val.map a.op) m) :=
  memberDatumAbFunctor_map_memberDiagHom B S hS Yi f hf D hL
    (i := j) (W := W) (V := V) a m

/-- Read across the identification `.memberDatumSheaf_obj`, the restriction map of the sheaf of
modules of a descent datum along the diagonal arrow induced by a morphism `a` of charts of the
member `Y j` is the restriction map of `D.F j` along `a`. -/
theorem memberDatumSheaf_map (j : I)
    (W V : (smallEtaleRingedSite B S hS (Yi j).1 (Yi j).2).C) (a : W ⟶ V)
    (y : ↥((memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.obj
      (Opposite.op (memberPair B S hS Yi f hf j V)))) :
    ModuleCat.Hom.hom (eqToHom (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh j W))
        ((memberSheafOfLaws B S hS Yi f hf hL hM hsh).val.map
          (memberDiagHom B S hS Yi f hf (i := j) (W := W) (V := V) a).op y) =
      (D.F j).val.map a.op
        (ModuleCat.Hom.hom
          (eqToHom (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh j V)) y) :=
  memberDatumAbFunctor_map_memberDiagHom_site B S hS Yi f hf D hL j W V a y

/-! ### The family of per-member isomorphisms of a descent datum -/

variable (M : Modules.{u, u} B S hS X.1 X.2)
  (β : (memberRestriction B S hS Yi f hf).obj M ≅
    memberSheafOfLaws B S hS Yi f hf hL hM hsh)

include β in
/-- At the sheaf of modules of a descent datum, the component of `.memberPerMemberIso` over a
chart `V` of the member `Y i` is the component of `β` over the corresponding object of the site of
the charts of the members. -/
theorem memberPerMemberIso_memberDatumSheaf_hom_val_app (i : I)
    (V : SmallEtale B S hS (Yi i).1) :
    (memberPerMemberIso B S hS Yi f hf D (memberSheafOfLaws B S hS Yi f hf hL hM hsh)
          (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh) M β
          (memberDatumSheaf_map B S hS Yi f hf D hL hM hsh) i).hom.val.app (Opposite.op V) =
      β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)) :=
  (memberPerMemberIso_hom_val_app B S hS Yi f hf D
        (memberSheafOfLaws B S hS Yi f hf hL hM hsh)
        (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh) M β
        (memberDatumSheaf_map B S hS Yi f hf D hL hM hsh) i V).trans
    ((congrArg (fun t => β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)) ≫ t)
          (eqToHom_memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh i V)).trans
      (Category.comp_id _))

include β in
/-- If the restriction of an `𝒪_X`-module `M` to the site of the charts of the members is
isomorphic, by `β`, to the sheaf of modules of a descent datum `D`, then there is a family of
isomorphisms `τ i` of the étale restriction of `M` to `Y i` with `D.F i` whose component over each
chart `V` of `Y i` is the component of `β` over the corresponding object of the site of the charts
of the members. -/
theorem exists_memberPerMemberIso :
    ∃ τ : ∀ i, (etaleModulePullback.{u, u} B S hS (f i) (hf i)).obj M ≅ D.F i,
      ∀ (i : I) (V : SmallEtale B S hS (Yi i).1),
        (τ i).hom.val.app (Opposite.op V) =
          β.hom.val.app (Opposite.op (memberPair B S hS Yi f hf i V)) :=
  ⟨fun i => memberPerMemberIso B S hS Yi f hf D
      (memberSheafOfLaws B S hS Yi f hf hL hM hsh)
      (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh) M β
      (memberDatumSheaf_map B S hS Yi f hf D hL hM hsh) i,
    memberPerMemberIso_memberDatumSheaf_hom_val_app B S hS Yi f hf D hL hM hsh M β⟩

include β in
/-- An `𝒪_X`-module whose restriction to the site of the charts of the members is isomorphic to
the sheaf of modules of a descent datum is quasi-coherent. -/
theorem isQuasicoherentOnSite_of_memberDatumSheaf_iso : M.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_memberPerMemberIso B S hS Yi f hf D
    (memberSheafOfLaws B S hS Yi f hf hL hM hsh)
    (memberDatumSheaf_obj B S hS Yi f hf D hL hM hsh) M β
    (memberDatumSheaf_map B S hS Yi f hf D hL hM hsh)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
