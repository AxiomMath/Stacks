module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Gluing.Postcompose
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.RestrictionComparison
public import StacksFrontier.CategoryTheory.Bicategory.Functor.Cat.Transport
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import StacksFrontier.CategoryTheory.Sites.Glueing.GlueingSheaves

/-!
# Étale descent for small étale sheaves, phrased with inverse images

Let `S` be a scheme of a big étale site `B` and `V k` a covering of `S` in its small étale site.
Sheaves on the slice sites of the small étale site of `S` satisfy descent along the covering
(Stacks 04TS, `CategoryTheory.GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver`).
This file moves that statement to the pseudofunctor
`AlgebraicGeometry.SmallEtaleGluing.pseudofunctor` of small étale inverse images on the big étale
site, where the members of the covering are the schemes `(V k).obj.left` with their structure
morphisms to `S`.

The passage is the one of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleGlobalDescent` for algebraic spaces,
in three steps.

* The pseudofunctor of sheaves on slices is transported along the slice equivalences
  `AlgebraicGeometry.smallEtaleEquivalenceOver`, giving a pseudofunctor on the small étale site of
  `S` whose fibres are the sheaf categories of the small étale sites of the members and whose
  transition functors are restrictions along composition with étale morphisms.
* A strong transformation with identity components identifies it with the restriction of the
  pseudofunctor of inverse images along the forgetful functor to the big étale site: inverse image
  along an étale morphism is restriction along composition with it, compatibly with identities
  and composition (`AlgebraicGeometry.SmallEtaleGluing.pullbackIsoRestriction_comp`).
* Descent data for the restricted pseudofunctor are descent data for the pseudofunctor itself,
  the forgetful functor preserving fibre products
  (`CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves`).

## Main definitions

* `AlgebraicGeometry.SmallEtaleGluing.transported` — the transported pseudofunctor.
* `AlgebraicGeometry.SmallEtaleGluing.strongTrans` — the strong transformation.

## Main results

* `AlgebraicGeometry.SmallEtaleGluing.isEquivalence_toDescentData` — étale descent for small
  étale sheaves along a covering, in the pseudofunctor of inverse images.

## References

* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
* [Stacks Project, Tag 04TR](https://stacks.math.columbia.edu/tag/04TR)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace AlgebraicGeometry

namespace SmallEtaleGluing

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A] (S : B.Scheme)

/-- The functor from the small étale site of `S` to the big étale site, sending an étale scheme
over `S` to its underlying scheme. -/
public abbrev forget : SmallEtale B S.1 S.property ⥤ B.Scheme :=
  SmallEtale.inclusion B S.1 S.property ⋙ BigEtaleOver.forget B S.1 S.property

/-- A morphism of the small étale site is étale. -/
public instance etale_forget_map {U W : SmallEtale B S.1 S.property} (a : U ⟶ W) :
    Etale (B.inclusion.map ((forget B S).map a)) :=
  B.etale_map_of_postcomp a.hom.left W.obj.hom U.obj.hom U.property W.property (Over.w a.hom)

/-- The category of sheaves on the small étale site of the scheme underlying an object of the
small étale site of `S`. -/
public abbrev fibre (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) : Cat :=
  Cat.of (Sheaf (SmallEtale.topology B ((forget B S).obj a.as.unop).1
    ((forget B S).obj a.as.unop).property) A)

/-- The slice equivalence `AlgebraicGeometry.smallEtaleEquivalenceOver` on sheaves: sheaves on
the slice of the small étale site of `S` over `U` are sheaves on the small étale site of the scheme
underlying `U`. -/
public abbrev fibreEquiv (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) :
    ((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).obj a ≌ fibre B A S a :=
  ((smallEtaleEquivalenceOver B S.1 S.property a.as.unop).sheafCongr
    (SmallEtale.topology B a.as.unop.obj.left.1 a.as.unop.obj.left.property)
    ((SmallEtale.topology B S.1 S.property).over a.as.unop) A).symm

/-- The pseudofunctor of sheaves on the slices of the small étale site of `S`, transported along
the slice equivalences to the sheaf categories of the small étale sites of the underlying
schemes. -/
public abbrev transported :
    Pseudofunctor (LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) Cat :=
  ((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).transport (fibre B A S)
    (fibreEquiv B A S)

variable [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- The identity constraint of the restricted pseudofunctor of inverse images, on components. -/
public theorem restrict_mapId_hom_app (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ)
    (M : ↑(((pseudofunctor B A).restrict (forget B S)).obj a)) :
    (((pseudofunctor B A).restrict (forget B S)).mapId a).hom.toNatTrans.app M =
      ((conjugateEquiv Adjunction.id
        ((smallEtaleBaseChange B (𝟙 ((forget B S).obj a.as.unop))).sheafAdjunctionContinuous
          A _ _)).symm (pushforwardId B A ((forget B S).obj a.as.unop)).inv).app M := by
  have hη : (((forget B S).op.toPseudofunctor).mapId a).hom = 𝟙 _ := Subsingleton.elim _ _
  show ((pseudofunctor B A).map₂ (((forget B S).op.toPseudofunctor).mapId a).hom ≫
    ((pseudofunctor B A).mapId _).hom).toNatTrans.app M = _
  have h0 : (pseudofunctor B A).map₂ (((forget B S).op.toPseudofunctor).mapId a).hom = 𝟙 _ := by
    rw [hη]
    exact (pseudofunctor B A).map₂_id _
  rw [h0]
  exact (congrArg (fun φ => φ.toNatTrans.app M)
    (Category.id_comp ((pseudofunctor B A).mapId _).hom)).trans rfl

/-- The identity constraint of the transported pseudofunctor is the strict identity comparison of
restriction along composition with an identity. -/
public theorem transported_mapId_hom_app (U : SmallEtale B S.1 S.property)
    (M : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A) :
    ((transported B A S).mapId ⟨op U⟩).hom.toNatTrans.app M =
      (postSheafIdIso B A ((forget B S).obj U)).hom.app M := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => ?_)
  have e1 : ∀ (N : Sheaf ((SmallEtale.topology B S.1 S.property).over U) A)
      (W : (Over U)ᵒᵖ),
      ((((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).mapId
        ⟨op U⟩).hom.toNatTrans.app N).hom.app W =
        N.obj.map ((Over.mapId U).inv.app W.unop).op :=
    fun _ _ => Category.comp_id _
  show ((((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).mapId
      ⟨op U⟩).hom.toNatTrans.app
      ((fibreEquiv B A S ⟨op U⟩).inverse.obj M)).hom.app
        (op ((smallEtaleEquivalenceOver B S.1 S.property U).functor.obj V.unop)) ≫
      M.obj.map ((smallEtaleEquivalenceOver B S.1 S.property U).unitIso.hom.app V.unop).op = _
  have e2 : ((postSheafIdIso B A ((forget B S).obj U)).hom.app M).hom.app V =
      M.obj.map ((postIdIso B ((forget B S).obj U)).inv.app V.unop).op :=
    Category.comp_id _
  refine (congrArg (· ≫ M.obj.map _) (e1 _ _)).trans
    (((M.obj.map_comp _ _).symm.trans (congrArg M.obj.map ?_)).trans e2.symm)
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp only [unop_comp, Quiver.Hom.unop_op, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left]
  exact (Category.id_comp _).trans rfl

/-- The composition constraint of the transported pseudofunctor is the strict composition
comparison of restriction along composition with étale morphisms. -/
public theorem transported_mapComp_hom_app {U V W : SmallEtale B S.1 S.property} (φ : V ⟶ U)
    (ψ : W ⟶ V) (M : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A) :
    ((transported B A S).mapComp φ.op.toLoc ψ.op.toLoc).hom.toNatTrans.app M =
      (postSheafCompIso B A ((forget B S).map ψ) ((forget B S).map φ)).inv.app M := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun X => ?_)
  simp only [Pseudofunctor.transport_mapComp, Pseudofunctor.transportMapComp_hom_app]
  have e1 : ∀ (N : Sheaf ((SmallEtale.topology B S.1 S.property).over U) A) (Y : (Over W)ᵒᵖ),
      ((((SmallEtale.topology B S.1 S.property).pseudofunctorOver A).mapComp φ.op.toLoc
        ψ.op.toLoc).hom.toNatTrans.app N).hom.app Y =
        N.obj.map ((Over.mapComp ψ φ).inv.app Y.unop).op :=
    fun _ _ => Category.comp_id _
  have e3 : ((postSheafCompIso B A ((forget B S).map ψ) ((forget B S).map φ)).inv.app M).hom.app
      X = M.obj.map ((postCompIso B ((forget B S).map ψ) ((forget B S).map φ)).hom.app X.unop).op :=
    Category.comp_id _
  rw [e3, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  refine (congrArg (· ≫ _) (e1 _ _)).trans
    (((M.obj.map_comp _ _).symm.trans (congrArg M.obj.map ?_)))
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  simp only [unop_comp, Quiver.Hom.unop_op, ObjectProperty.FullSubcategory.comp_hom,
    Over.comp_left, Functor.op_map]
  exact (Category.id_comp _).trans rfl

/-- The composition constraint of the restricted pseudofunctor of inverse images, on
components. -/
public theorem restrict_mapComp_hom_app {U V W : SmallEtale B S.1 S.property} (φ : V ⟶ U)
    (ψ : W ⟶ V) (M : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A) :
    (((pseudofunctor B A).restrict (forget B S)).mapComp φ.op.toLoc ψ.op.toLoc).hom.toNatTrans.app
        M =
      (smallEtaleSheafPullbackCompIso B _ _ _ ((forget B S).map ψ) ((forget B S).map φ) A).inv.app
        M := by
  have hη : (((forget B S).op.toPseudofunctor).mapComp φ.op.toLoc ψ.op.toLoc).hom = 𝟙 _ :=
    Subsingleton.elim _ _
  show ((pseudofunctor B A).map₂ (((forget B S).op.toPseudofunctor).mapComp φ.op.toLoc
    ψ.op.toLoc).hom ≫ ((pseudofunctor B A).mapComp ((forget B S).map φ).op.toLoc
      ((forget B S).map ψ).op.toLoc).hom).toNatTrans.app M = _
  have h0 : (pseudofunctor B A).map₂ (((forget B S).op.toPseudofunctor).mapComp φ.op.toLoc
      ψ.op.toLoc).hom = 𝟙 _ := by
    rw [hη]
    exact (pseudofunctor B A).map₂_id _
  rw [h0]
  exact (congrArg (fun φ => φ.toNatTrans.app M)
    (Category.id_comp ((pseudofunctor B A).mapComp ((forget B S).map φ).op.toLoc
      ((forget B S).map ψ).op.toLoc).hom)).trans rfl

/-- The identification of inverse image with restriction is compatible with composition, in the
form of inverses on components. -/
private theorem pullbackIsoRestriction_comp_inv_app {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (B.inclusion.map f)] [Etale (B.inclusion.map g)] [Etale (B.inclusion.map (f ≫ g))]
    (M : Sheaf (SmallEtale.topology B Z.1 Z.property) A) :
    (pullbackIsoRestriction B A (f ≫ g)).inv.app M ≫
        (smallEtaleSheafPullbackCompIso B X Y Z f g A).inv.app M =
      (postSheafCompIso B A f g).inv.app M ≫
        (pullbackIsoRestriction B A f).inv.app
          (((post B g).sheafPushforwardContinuous A _ _).obj M) ≫
        (smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).inv.app M) := by
  have h2 := NatTrans.congr_app (pullbackIsoRestriction_comp B A f g) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h2
  have hX : ((smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).hom.app M) ≫
      (pullbackIsoRestriction B A f).hom.app
        (((post B g).sheafPushforwardContinuous A _ _).obj M)) ≫
      ((pullbackIsoRestriction B A f).inv.app
        (((post B g).sheafPushforwardContinuous A _ _).obj M) ≫
      (smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).inv.app M)) = 𝟙 _ := by
    simp [← Functor.map_comp]
  calc _ = (pullbackIsoRestriction B A (f ≫ g)).inv.app M ≫
        (smallEtaleSheafPullbackCompIso B X Y Z f g A).inv.app M ≫
        (((smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).hom.app M) ≫
          (pullbackIsoRestriction B A f).hom.app
            (((post B g).sheafPushforwardContinuous A _ _).obj M)) ≫
          ((pullbackIsoRestriction B A f).inv.app
            (((post B g).sheafPushforwardContinuous A _ _).obj M) ≫
          (smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).inv.app M))) := by
        rw [hX]
        exact congrArg _ (Category.comp_id _).symm
    _ = (pullbackIsoRestriction B A (f ≫ g)).inv.app M ≫
        ((pullbackIsoRestriction B A (f ≫ g)).hom.app M ≫ (postSheafCompIso B A f g).inv.app M) ≫
          ((pullbackIsoRestriction B A f).inv.app
            (((post B g).sheafPushforwardContinuous A _ _).obj M) ≫
          (smallEtaleSheafPullback B A f).map ((pullbackIsoRestriction B A g).inv.app M)) := by
        rw [← h2]
        simp only [Category.assoc]
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- **The transported pseudofunctor of sheaves on slices is the pseudofunctor of inverse
images.** The strong transformation with identity components whose naturality constraint is the
identification `AlgebraicGeometry.SmallEtaleGluing.pullbackIsoRestriction` of the inverse image
along an étale morphism with restriction along composition with it. -/
public def strongTrans :
    Pseudofunctor.StrongTrans (transported B A S) ((pseudofunctor B A).restrict (forget B S)) where
  app a := 𝟙 _
  naturality {a b} φ :=
    Cat.Hom.isoMk (pullbackIsoRestriction B A ((forget B S).map φ.as.unop)).symm
  naturality_naturality := by
    intro a b f g η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    rw [Pseudofunctor.map₂_eq_eqToHom (transported B A S),
      Pseudofunctor.map₂_eq_eqToHom ((pseudofunctor B A).restrict (forget B S))]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  naturality_id := by
    rintro ⟨⟨U⟩⟩
    ext M
    change (pullbackIsoRestriction B A (𝟙 ((forget B S).obj U))).inv.app M ≫
        (((pseudofunctor B A).restrict (forget B S)).mapId ⟨op U⟩).hom.toNatTrans.app M =
      ((transported B A S).mapId ⟨op U⟩).hom.toNatTrans.app M ≫ 𝟙 _ ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id, restrict_mapId_hom_app B A S ⟨op U⟩ M,
      transported_mapId_hom_app B A S U M,
      NatTrans.congr_app (pullbackIsoRestriction_id B A ((forget B S).obj U)) M, NatTrans.comp_app]
    exact Iso.inv_hom_id_app_assoc _ _ _
  naturality_comp := by
    rintro ⟨⟨U⟩⟩ ⟨⟨V⟩⟩ ⟨⟨W⟩⟩ ⟨φ⟩ ⟨ψ⟩
    ext M
    change (pullbackIsoRestriction B A ((forget B S).map ψ.unop ≫
          (forget B S).map φ.unop)).inv.app M ≫
        (((pseudofunctor B A).restrict (forget B S)).mapComp φ.unop.op.toLoc
          ψ.unop.op.toLoc).hom.toNatTrans.app M =
      ((transported B A S).mapComp φ.unop.op.toLoc ψ.unop.op.toLoc).hom.toNatTrans.app M ≫ 𝟙 _ ≫
        (pullbackIsoRestriction B A ((forget B S).map ψ.unop)).inv.app
          (((post B ((forget B S).map φ.unop)).sheafPushforwardContinuous A _ _).obj M) ≫ 𝟙 _ ≫
        (smallEtaleSheafPullback B A ((forget B S).map ψ.unop)).map
          ((pullbackIsoRestriction B A ((forget B S).map φ.unop)).inv.app M) ≫ 𝟙 _
    rw [restrict_mapComp_hom_app B A S φ.unop ψ.unop M,
      transported_mapComp_hom_app B A S φ.unop ψ.unop M]
    simp only [Category.id_comp, Category.comp_id]
    exact pullbackIsoRestriction_comp_inv_app B A _ _ M

/-- The components of `AlgebraicGeometry.SmallEtaleGluing.strongTrans` are equivalences, being
identities. -/
public instance isEquivalence_strongTrans_app
    (a : LocallyDiscrete (SmallEtale B S.1 S.property)ᵒᵖ) :
    ((strongTrans B A S).app a).toFunctor.IsEquivalence :=
  Functor.isEquivalence_refl

/-- **Étale descent for small étale sheaves, phrased with inverse images.** For a family of
objects `V k` of the small étale site of `S` covering its final object, the canonical functor from
sheaves on the small étale site of `S` to descent data for the structure morphisms of the `V k`,
in the pseudofunctor of small étale inverse images, is an equivalence. -/
public theorem isEquivalence_toDescentData [HasLimitsOfSize.{u + 1, u + 1} A]
    {ι : Type*} (V : ι → SmallEtale B S.1 S.property)
    (hV : Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
      SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property)) :
    ((pseudofunctor B A).toDescentData (fun k => (V k).obj.hom)).IsEquivalence := by
  let g := fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)
  exact (Pseudofunctor.isEquivalence_toDescentData_restrict_iff_of_preserves
    (pseudofunctor B A) (forget B S) g).mp
      (((strongTrans B A S).isEquivalence_toDescentData_iff g
        (isEquivalence_strongTrans_app B A S)).mp
        ((Pseudofunctor.isEquivalence_toDescentData_transport_iff _ _ _ g).mp
          (GrothendieckTopology.isEquivalence_toDescentData_pseudofunctorOver _ A g hV)))

end SmallEtaleGluing

end AlgebraicGeometry

end
