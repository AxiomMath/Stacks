module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullback.RingTransport
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Transporting a module structure along a finite-product-preserving functor

The additive group operations and the scalar multiplication of a sheaf of modules on its
underlying sheaf of sets, and the additive group and module structures `moduleObjAddCommGroup`,
`moduleObjModule` they induce on the image of that sheaf under a finite-product-preserving
functor to types, over the transported ring `ringObjRing`.
-/

@[expose] public section

open CategoryTheory Limits

universe t t' w v u

namespace CategoryTheory.Sheaf

open _root_.CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ## The underlying sheaf of sets of a sheaf of modules -/

section ModuleOperations

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w})

/-- The functor taking a sheaf of modules to the underlying sheaf of sets. -/
noncomputable abbrev moduleSheafFunctor : SheafOfModules.{w} R ⥤ Sheaf J (Type w) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat.{w})

/-- The underlying sheaf of sets of a sheaf of modules. -/
noncomputable abbrev moduleSheaf (G : SheafOfModules.{w} R) : Sheaf J (Type w) :=
  (moduleSheafFunctor R).obj G

variable (G : SheafOfModules.{w} R)

/-- Addition on the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleAddHom : moduleSheaf R G ⨯ moduleSheaf R G ⟶ moduleSheaf R G :=
  binaryOpHom (fun X (a b : G.val.obj X) ↦ a + b) (fun g a b ↦ (G.val.map g).hom.map_add a b)

/-- Negation on the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleNegHom : moduleSheaf R G ⟶ moduleSheaf R G :=
  unaryOpHom (fun X (a : G.val.obj X) ↦ -a) (fun g a ↦ (G.val.map g).hom.map_neg a)

/-- The zero section of the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleZeroHom : ⊤_ (Sheaf J (Type w)) ⟶ moduleSheaf R G :=
  constHom (fun X ↦ (0 : G.val.obj X)) (fun g ↦ (G.val.map g).hom.map_zero)

/-- Scalar multiplication on the underlying sheaves of sets of a sheaf of rings and a sheaf of
modules over it. -/
noncomputable def moduleSMulHom : ringSheaf R ⨯ moduleSheaf R G ⟶ moduleSheaf R G :=
  binaryOpHom (fun X (r : R.obj.obj X) (m : G.val.obj X) ↦ r • m)
    (fun g r m ↦ G.val.map_smul g r m)

/-- Sections over `X` of the underlying sheaf of sets of a sheaf of modules form an additive
commutative group: they are the sections of the sheaf of modules itself. -/
noncomputable instance moduleSectionsAddCommGroup (X : Cᵒᵖ) :
    AddCommGroup ((sectionsFunctor J X).obj (moduleSheaf R G)) :=
  inferInstanceAs (AddCommGroup (G.val.obj X))

/-- Sections over `X` of the underlying sheaf of sets of a sheaf of modules form a module over
the sections of the sheaf of rings. -/
noncomputable instance moduleSectionsModule (X : Cᵒᵖ) :
    Module ((sectionsFunctor J X).obj (ringSheaf R))
      ((sectionsFunctor J X).obj (moduleSheaf R G)) :=
  inferInstanceAs (Module (R.obj.obj X) (G.val.obj X))

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections over `X`, `moduleAddHom R G` sends the pair of `a` and `b` to `a + b`. -/
@[simp]
lemma sectionsFunctor_map_moduleAddHom (X : Cᵒᵖ)
    (a b : (sectionsFunctor J X).obj (moduleSheaf R G)) :
    (sectionsFunctor J X).map (moduleAddHom R G)
        (prodObjMk (A := moduleSheaf R G) (B := moduleSheaf R G) a b) = a + b :=
  sectionsFunctor_map_binaryOpHom (A := moduleSheaf R G) (B := moduleSheaf R G)
    (E := moduleSheaf R G) _ _ X a b

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections over `X`, `moduleNegHom R G` sends `a` to `-a`. -/
@[simp]
lemma sectionsFunctor_map_moduleNegHom (X : Cᵒᵖ)
    (a : (sectionsFunctor J X).obj (moduleSheaf R G)) :
    (sectionsFunctor J X).map (moduleNegHom R G) a = -a := rfl

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections over `X`, `moduleZeroHom R G` takes the value `0`. -/
@[simp]
lemma sectionsFunctor_map_moduleZeroHom (X : Cᵒᵖ)
    (p : (sectionsFunctor J X).obj (⊤_ (Sheaf J (Type w)))) :
    (sectionsFunctor J X).map (moduleZeroHom R G) p =
      (0 : (sectionsFunctor J X).obj (moduleSheaf R G)) := rfl

/-- On sections over `X`, `moduleSMulHom R G` sends the pair of `r` and `m` to `r • m`. -/
@[simp]
lemma sectionsFunctor_map_moduleSMulHom (X : Cᵒᵖ)
    (r : (sectionsFunctor J X).obj (ringSheaf R))
    (m : (sectionsFunctor J X).obj (moduleSheaf R G)) :
    (sectionsFunctor J X).map (moduleSMulHom R G)
        (prodObjMk (A := ringSheaf R) (B := moduleSheaf R G) r m) = r • m :=
  sectionsFunctor_map_binaryOpHom (A := ringSheaf R) (B := moduleSheaf R G)
    (E := moduleSheaf R G) _ _ X r m

variable {Z : Sheaf J (Type w)}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Associativity of `moduleAddHom R G`, for morphisms from a sheaf of types `Z`. -/
lemma moduleAddHom_assoc (a b c : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (Limits.prod.lift a b ≫ moduleAddHom R G) c ≫ moduleAddHom R G =
      Limits.prod.lift a (Limits.prod.lift b c ≫ moduleAddHom R G) ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  exact add_assoc _ _ _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- `moduleZeroHom R G` is a left identity for `moduleAddHom R G`. -/
lemma moduleAddHom_zero_add (a : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (Limits.terminal.from Z ≫ moduleZeroHom R G) a ≫ moduleAddHom R G = a := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    sectionsFunctor_map_moduleAddHom, sectionsFunctor_map_moduleZeroHom]
  exact zero_add _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Composing with `moduleNegHom R G` gives a left inverse for `moduleAddHom R G`. -/
lemma moduleAddHom_neg_add_cancel (a : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (a ≫ moduleNegHom R G) a ≫ moduleAddHom R G =
      Limits.terminal.from Z ≫ moduleZeroHom R G := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    sectionsFunctor_map_moduleAddHom, sectionsFunctor_map_moduleNegHom,
    sectionsFunctor_map_moduleZeroHom]
  exact neg_add_cancel _

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- Commutativity of `moduleAddHom R G`. -/
lemma moduleAddHom_comm (a b : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift a b ≫ moduleAddHom R G = Limits.prod.lift b a ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom]
  exact add_comm _ _

/-- The unit `ringOneHom R` acts trivially under `moduleSMulHom R G`. -/
lemma moduleSMulHom_one_smul (m : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (Limits.terminal.from Z ≫ ringOneHom R) m ≫ moduleSMulHom R G = m := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, Functor.map_terminalFrom_apply,
    sectionsFunctor_map_moduleSMulHom, sectionsFunctor_map_ringOneHom]
  exact one_smul _ _

/-- Scalar multiplication `moduleSMulHom R G` satisfies `(r * s) • m = r • (s • m)`. -/
lemma moduleSMulHom_mul_smul (r s : Z ⟶ ringSheaf R) (m : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (Limits.prod.lift r s ≫ ringMulHom R) m ≫ moduleSMulHom R G =
      Limits.prod.lift r (Limits.prod.lift s m ≫ moduleSMulHom R G) ≫ moduleSMulHom R G := by
  refine hom_ext_sections (fun X t ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom,
    sectionsFunctor_map_ringMulHom]
  exact mul_smul _ _ _

/-- Scalar multiplication `moduleSMulHom R G` satisfies `r • (m + n) = r • m + r • n`. -/
lemma moduleSMulHom_smul_add (r : Z ⟶ ringSheaf R) (m n : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift r (Limits.prod.lift m n ≫ moduleAddHom R G) ≫ moduleSMulHom R G =
      Limits.prod.lift (Limits.prod.lift r m ≫ moduleSMulHom R G)
        (Limits.prod.lift r n ≫ moduleSMulHom R G) ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun X t ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom,
    sectionsFunctor_map_moduleAddHom]
  exact smul_add _ _ _

/-- Scalar multiplication `moduleSMulHom R G` satisfies `(r + s) • m = r • m + s • m`. -/
lemma moduleSMulHom_add_smul (r s : Z ⟶ ringSheaf R) (m : Z ⟶ moduleSheaf R G) :
    Limits.prod.lift (Limits.prod.lift r s ≫ ringAddHom R) m ≫ moduleSMulHom R G =
      Limits.prod.lift (Limits.prod.lift r m ≫ moduleSMulHom R G)
        (Limits.prod.lift s m ≫ moduleSMulHom R G) ≫ moduleAddHom R G := by
  refine hom_ext_sections (fun X t ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom,
    sectionsFunctor_map_moduleAddHom, sectionsFunctor_map_ringAddHom]
  exact add_smul _ _ _

variable {G} {G' : SheafOfModules.{w} R} (φ : G ⟶ G')

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections over `X`, the morphism of underlying sheaves of types of a morphism `φ` of sheaves
of modules is additive. -/
@[simp]
lemma sectionsFunctor_map_moduleSheafFunctor_map_add (X : Cᵒᵖ)
    (x y : (sectionsFunctor J X).obj (moduleSheaf R G)) :
    (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ) (x + y) =
      (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ) x +
        (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ) y :=
  (φ.val.app X).hom.map_add x y

/-- On sections over `X`, the morphism of underlying sheaves of types of a morphism `φ` of sheaves
of modules commutes with scalar multiplication. -/
@[simp]
lemma sectionsFunctor_map_moduleSheafFunctor_map_smul (X : Cᵒᵖ)
    (r : (sectionsFunctor J X).obj (ringSheaf R))
    (x : (sectionsFunctor J X).obj (moduleSheaf R G)) :
    (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ) (r • x) =
      r • (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ) x :=
  (φ.val.app X).hom.map_smul r x

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The morphism of underlying sheaves of types of `φ` commutes with `moduleAddHom`. -/
lemma moduleSheafFunctor_map_add (a b : Z ⟶ moduleSheaf R G) :
    (Limits.prod.lift a b ≫ moduleAddHom R G) ≫ (moduleSheafFunctor R).map φ =
      Limits.prod.lift (a ≫ (moduleSheafFunctor R).map φ)
        (b ≫ (moduleSheafFunctor R).map φ) ≫ moduleAddHom R G' := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleAddHom,
    sectionsFunctor_map_moduleSheafFunctor_map_add]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- On sections over `X`, the morphism of underlying sheaves of types of a morphism `φ` of sheaves
of modules sends `0` to `0`. -/
@[simp]
lemma sectionsFunctor_map_moduleSheafFunctor_map_zero (X : Cᵒᵖ) :
    (sectionsFunctor J X).map ((moduleSheafFunctor R).map φ)
        (0 : (sectionsFunctor J X).obj (moduleSheaf R G)) = 0 :=
  (φ.val.app X).hom.map_zero

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The morphism of underlying sheaves of types of `φ` sends the zero section of `G` to that
of `G'`. -/
lemma moduleSheafFunctor_map_zero :
    moduleZeroHom R G ≫ (moduleSheafFunctor R).map φ = moduleZeroHom R G' := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, sectionsFunctor_map_moduleZeroHom,
    sectionsFunctor_map_moduleSheafFunctor_map_zero]

/-- The morphism of underlying sheaves of types of `φ` commutes with `moduleSMulHom`. -/
lemma moduleSheafFunctor_map_smul (r : Z ⟶ ringSheaf R) (m : Z ⟶ moduleSheaf R G) :
    (Limits.prod.lift r m ≫ moduleSMulHom R G) ≫ (moduleSheafFunctor R).map φ =
      Limits.prod.lift r (m ≫ (moduleSheafFunctor R).map φ) ≫ moduleSMulHom R G' := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [Functor.map_comp_apply, Functor.map_lift_apply, sectionsFunctor_map_moduleSMulHom,
    sectionsFunctor_map_moduleSheafFunctor_map_smul]

end ModuleOperations

/-! ## Transporting the module structure along a finite-product-preserving functor -/

section ModuleTransport

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (R : Sheaf J RingCat.{w}) (G : SheafOfModules.{w} R)
  (P : Sheaf J (Type w) ⥤ Type t) [PreservesFiniteProducts P]

/-- Addition transported to the image of the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleAddObj (x y : P.obj (moduleSheaf R G)) : P.obj (moduleSheaf R G) :=
  P.map (moduleAddHom R G) (prodObjMk x y)

/-- Negation transported to the image of the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleNegObj (x : P.obj (moduleSheaf R G)) : P.obj (moduleSheaf R G) :=
  P.map (moduleNegHom R G) x

/-- The zero of the image of the underlying sheaf of sets of a sheaf of modules. -/
noncomputable def moduleZeroObj : P.obj (moduleSheaf R G) := P.map (moduleZeroHom R G) default

/-- Scalar multiplication transported to the images of the underlying sheaves of sets. -/
noncomputable def moduleSMulObj (r : P.obj (ringSheaf R)) (x : P.obj (moduleSheaf R G)) :
    P.obj (moduleSheaf R G) :=
  P.map (moduleSMulHom R G) (prodObjMk r x)

/-- Equal morphisms have equal images under a functor to types. -/
private lemma map_apply_congr {D : Type*} [Category D] {P : D ⥤ Type t} {X Y : D}
    {f g : X ⟶ Y} (h : f = g) (x : P.obj X) : P.map f x = P.map g x := by
  rw [h]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The transported addition `moduleAddObj R G P` is associative. -/
lemma moduleAddObj_assoc (x y z : P.obj (moduleSheaf R G)) :
    moduleAddObj R G P (moduleAddObj R G P x y) z =
      moduleAddObj R G P x (moduleAddObj R G P y z) := by
  simpa [moduleAddObj] using map_apply_congr
    (moduleAddHom_assoc R (G := G) (Z := moduleSheaf R G ⨯ (moduleSheaf R G ⨯ moduleSheaf R G))
      Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) (Limits.prod.snd ≫ Limits.prod.snd))
    (prodObjMk (A := moduleSheaf R G) x (prodObjMk y z))

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- `moduleZeroObj R G P` is a left identity for `moduleAddObj R G P`. -/
lemma moduleAddObj_zero_add (x : P.obj (moduleSheaf R G)) :
    moduleAddObj R G P (moduleZeroObj R G P) x = x := by
  simpa [moduleAddObj, moduleZeroObj] using map_apply_congr
    (moduleAddHom_zero_add R (G := G) (Z := moduleSheaf R G) (𝟙 _))
    x

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- `moduleNegObj R G P x` is a left inverse of `x` for `moduleAddObj R G P`. -/
lemma moduleAddObj_neg_add_cancel (x : P.obj (moduleSheaf R G)) :
    moduleAddObj R G P (moduleNegObj R G P x) x = moduleZeroObj R G P := by
  simpa [moduleAddObj, moduleNegObj, moduleZeroObj] using map_apply_congr
    (moduleAddHom_neg_add_cancel R (G := G) (Z := moduleSheaf R G) (𝟙 _))
    x

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The transported addition `moduleAddObj R G P` is commutative. -/
lemma moduleAddObj_comm (x y : P.obj (moduleSheaf R G)) :
    moduleAddObj R G P x y = moduleAddObj R G P y x := by
  simpa [moduleAddObj] using map_apply_congr
    (moduleAddHom_comm R (G := G) (Z := moduleSheaf R G ⨯ moduleSheaf R G)
      Limits.prod.fst Limits.prod.snd)
    (prodObjMk (A := moduleSheaf R G) (B := moduleSheaf R G) x y)

/-- The transported unit `ringOneObj R P` acts trivially under `moduleSMulObj R G P`. -/
lemma moduleSMulObj_one_smul (x : P.obj (moduleSheaf R G)) :
    moduleSMulObj R G P (ringOneObj R P) x = x := by
  simpa [moduleSMulObj, ringOneObj] using map_apply_congr
    (moduleSMulHom_one_smul R (G := G) (Z := moduleSheaf R G) (𝟙 _))
    x

/-- The transported scalar multiplication satisfies `(r * s) • x = r • (s • x)`. -/
lemma moduleSMulObj_mul_smul (r s : P.obj (ringSheaf R)) (x : P.obj (moduleSheaf R G)) :
    moduleSMulObj R G P (ringMulObj R P r s) x =
      moduleSMulObj R G P r (moduleSMulObj R G P s x) := by
  simpa [moduleSMulObj, ringMulObj] using map_apply_congr
    (moduleSMulHom_mul_smul R (G := G) (Z := ringSheaf R ⨯ (ringSheaf R ⨯ moduleSheaf R G))
      Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) (Limits.prod.snd ≫ Limits.prod.snd))
    (prodObjMk (A := ringSheaf R) r (prodObjMk s x))

/-- The transported scalar multiplication satisfies `r • (x + y) = r • x + r • y`. -/
lemma moduleSMulObj_smul_add (r : P.obj (ringSheaf R)) (x y : P.obj (moduleSheaf R G)) :
    moduleSMulObj R G P r (moduleAddObj R G P x y) =
      moduleAddObj R G P (moduleSMulObj R G P r x) (moduleSMulObj R G P r y) := by
  simpa [moduleSMulObj, moduleAddObj] using map_apply_congr
    (moduleSMulHom_smul_add R (G := G)
      (Z := ringSheaf R ⨯ (moduleSheaf R G ⨯ moduleSheaf R G))
      Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) (Limits.prod.snd ≫ Limits.prod.snd))
    (prodObjMk (A := ringSheaf R) r (prodObjMk x y))

/-- The transported scalar multiplication satisfies `(r + s) • x = r • x + s • x`. -/
lemma moduleSMulObj_add_smul (r s : P.obj (ringSheaf R)) (x : P.obj (moduleSheaf R G)) :
    moduleSMulObj R G P (ringAddObj R P r s) x =
      moduleAddObj R G P (moduleSMulObj R G P r x) (moduleSMulObj R G P s x) := by
  simpa [moduleSMulObj, ringAddObj, moduleAddObj] using map_apply_congr
    (moduleSMulHom_add_smul R (G := G) (Z := ringSheaf R ⨯ (ringSheaf R ⨯ moduleSheaf R G))
      Limits.prod.fst (Limits.prod.snd ≫ Limits.prod.fst) (Limits.prod.snd ≫ Limits.prod.snd))
    (prodObjMk (A := ringSheaf R) r (prodObjMk s x))

/-- The image of the underlying sheaf of sets of a sheaf of modules under a functor to types
preserving finite products is an additive commutative group. -/
@[instance_reducible]
noncomputable def moduleObjAddCommGroup : AddCommGroup (P.obj (moduleSheaf R G)) :=
  letI : Add (P.obj (moduleSheaf R G)) := ⟨moduleAddObj R G P⟩
  letI : Neg (P.obj (moduleSheaf R G)) := ⟨moduleNegObj R G P⟩
  letI : Zero (P.obj (moduleSheaf R G)) := ⟨moduleZeroObj R G P⟩
  letI : AddGroup (P.obj (moduleSheaf R G)) :=
    AddGroup.ofLeftAxioms (moduleAddObj_assoc R G P) (moduleAddObj_zero_add R G P)
      (moduleAddObj_neg_add_cancel R G P)
  { (inferInstance : AddGroup (P.obj (moduleSheaf R G))) with
      add_comm := moduleAddObj_comm R G P }

/-- The image of the underlying sheaf of sets of a sheaf of modules is a module over the image of
the underlying sheaf of sets of the sheaf of rings, with the transported scalar
multiplication. This is the algebraic form of the main construction: inverse image, being left
exact, transports the scalar action. -/
@[instance_reducible]
noncomputable def moduleObjModule :
    letI := ringObjRing R P
    letI := moduleObjAddCommGroup R G P
    Module (P.obj (ringSheaf R)) (P.obj (moduleSheaf R G)) :=
  letI := ringObjRing R P
  letI := moduleObjAddCommGroup R G P
  letI : SMul (P.obj (ringSheaf R)) (P.obj (moduleSheaf R G)) := ⟨moduleSMulObj R G P⟩
  Module.ofMinimalAxioms (moduleSMulObj_smul_add R G P) (moduleSMulObj_add_smul R G P)
    (moduleSMulObj_mul_smul R G P) (moduleSMulObj_one_smul R G P)

variable {P} {Q : Sheaf J (Type w) ⥤ Type t} [PreservesFiniteProducts Q] (θ : P ⟶ Q)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A natural transformation `θ : P ⟶ Q` commutes with the transported module additions. -/
lemma moduleAddObj_naturality (x y : P.obj (moduleSheaf R G)) :
    θ.app (moduleSheaf R G) (moduleAddObj R G P x y) =
      moduleAddObj R G Q (θ.app _ x) (θ.app _ y) := by
  rw [moduleAddObj, moduleAddObj, natTrans_app_map_apply, prodObjMk_naturality]

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- A natural transformation `θ : P ⟶ Q` sends the transported module zero to the transported
module zero. -/
lemma moduleZeroObj_naturality :
    θ.app (moduleSheaf R G) (moduleZeroObj R G P) = moduleZeroObj R G Q := by
  rw [moduleZeroObj, moduleZeroObj, natTrans_app_map_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- A natural transformation `θ : P ⟶ Q` commutes with the transported scalar multiplications. -/
lemma moduleSMulObj_naturality (r : P.obj (ringSheaf R)) (x : P.obj (moduleSheaf R G)) :
    θ.app (moduleSheaf R G) (moduleSMulObj R G P r x) =
      moduleSMulObj R G Q (θ.app _ r) (θ.app _ x) := by
  rw [moduleSMulObj, moduleSMulObj, natTrans_app_map_apply, prodObjMk_naturality]

section Map

variable {G} {G' : SheafOfModules.{w} R} (φ : G ⟶ G') (P)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The image under `P` of the morphism of underlying sheaves of types of `φ` commutes with the
transported additions. -/
lemma map_moduleSheafFunctor_map_addObj (x y : P.obj (moduleSheaf R G)) :
    P.map ((moduleSheafFunctor R).map φ) (moduleAddObj R G P x y) =
      moduleAddObj R G' P (P.map ((moduleSheafFunctor R).map φ) x)
        (P.map ((moduleSheafFunctor R).map φ) y) := by
  simpa [moduleAddObj] using map_apply_congr
    (moduleSheafFunctor_map_add R φ (Z := moduleSheaf R G ⨯ moduleSheaf R G)
      Limits.prod.fst Limits.prod.snd)
    (prodObjMk (A := moduleSheaf R G) (B := moduleSheaf R G) x y)

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The image under `P` of the morphism of underlying sheaves of types of `φ` sends the transported
zero to the transported zero. -/
lemma map_moduleSheafFunctor_map_zeroObj :
    P.map ((moduleSheafFunctor R).map φ) (moduleZeroObj R G P) = moduleZeroObj R G' P := by
  simpa [moduleZeroObj] using map_apply_congr
    (moduleSheafFunctor_map_zero R φ)
    (default : P.obj (⊤_ (Sheaf J (Type w))))

/-- The image under `P` of the morphism of underlying sheaves of types of `φ` commutes with the
transported scalar multiplications. -/
lemma map_moduleSheafFunctor_map_smulObj (r : P.obj (ringSheaf R))
    (x : P.obj (moduleSheaf R G)) :
    P.map ((moduleSheafFunctor R).map φ) (moduleSMulObj R G P r x) =
      moduleSMulObj R G' P r (P.map ((moduleSheafFunctor R).map φ) x) := by
  simpa [moduleSMulObj] using map_apply_congr
    (moduleSheafFunctor_map_smul R φ (Z := ringSheaf R ⨯ moduleSheaf R G)
      Limits.prod.fst Limits.prod.snd)
    (prodObjMk (A := ringSheaf R) (B := moduleSheaf R G) r x)

end Map

/-- A natural transformation of finite-product-preserving functors to types induces an additive
map between the transported additive group structures. -/
noncomputable def moduleObjHom :
    letI := moduleObjAddCommGroup R G P
    letI := moduleObjAddCommGroup R G Q
    P.obj (moduleSheaf R G) →+ Q.obj (moduleSheaf R G) :=
  letI := moduleObjAddCommGroup R G P
  letI := moduleObjAddCommGroup R G Q
  { toFun := θ.app (moduleSheaf R G)
    map_zero' := moduleZeroObj_naturality R G θ
    map_add' := moduleAddObj_naturality R G θ }

end ModuleTransport

end CategoryTheory.Sheaf
